import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 179` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT179 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((179 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-4681/8000 : ℚ) : ℝ))

theorem st179_c1 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((833643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 365703/2500000) (δ := 201/1000000000) (ψ := -4681/8000) 179 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t1 : ((833593/1000000 : ℚ) : ℝ) ≤ stT179 1 := by
  have hc : ((833593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((833593/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((833593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c2 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((107177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2513103/10000000) (δ := 1809/200000000) (ψ := -4681/8000) 179 20
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t2 : ((757785037189/2000000000000 : ℚ) : ℝ) ≤ stT179 2 := by
  have hc : ((107167/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((757785037189/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((107167/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c3 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-193823/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6144933/10000000) (δ := 8979/1000000000) (ψ := -4681/8000) 179 31
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t3 : ((-2238219681513/5000000000000 : ℚ) : ℝ) ≤ stT179 3 := by
  have hc : ((-387671/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2238219681513/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-387671/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c4 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-213653/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6488997/10000000) (δ := 4557/500000000) (ψ := -4681/8000) 179 40
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t4 : ((-2136655427331/5000000000000 : ℚ) : ℝ) ≤ stT179 4 := by
  have hc : ((-427331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2136655427331/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-427331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c5 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((938683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176003/2000000) (δ := 1129/125000000) (ψ := -4681/8000) 179 46
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t5 : ((839538698291/2000000000000 : ℚ) : ℝ) ≤ stT179 5 := by
  have hc : ((938633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((839538698291/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((938633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c6 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((646647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27113/125000) (δ := 2267/250000000) (ψ := -4681/8000) 179 51
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t6 : ((1319860306877/5000000000000 : ℚ) : ℝ) ≤ stT179 6 := by
  have hc : ((646597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1319860306877/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((646597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c7 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-61419/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3694169/5000000) (δ := 569/62500000) (ψ := -4681/8000) 179 56
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t7 : ((-371446124233/1000000000000 : ℚ) : ℝ) ≤ stT179 7 := by
  have hc : ((-491377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371446124233/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-491377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c8 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-125613/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5243073/10000000) (δ := 4539/500000000) (ψ := -4681/8000) 179 59
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t8 : ((-444153226517/2500000000000 : ℚ) : ℝ) ≤ stT179 8 := by
  have hc : ((-251251/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-444153226517/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-251251/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c9 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-372367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4880887/10000000) (δ := 4527/500000000) (ψ := -4681/8000) 179 63
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t9 : ((-620695124139/5000000000000 : ℚ) : ℝ) ≤ stT179 9 := by
  have hc : ((-372417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-620695124139/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-372417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c10 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-363093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4855953/10000000) (δ := 363/40000000) (ψ := -4681/8000) 179 66
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t10 : ((-574179559877/5000000000000 : ℚ) : ℝ) ≤ stT179 10 := by
  have hc : ((-363143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-574179559877/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-363143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c11 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-415521/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1275887/2000000) (δ := 909/100000000) (ψ := -4681/8000) 179 68
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t11 : ((-313229640561/1250000000000 : ℚ) : ℝ) ≤ stT179 11 := by
  have hc : ((-207773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-313229640561/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-207773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c12 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((149999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -903427/5000000) (δ := 2273/250000000) (ψ := -4681/8000) 179 71
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t12 : ((432980895739/2000000000000 : ℚ) : ℝ) ≤ stT179 12 := by
  have hc : ((149989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432980895739/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((149989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c13 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((253743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 324541/1250000) (δ := 8977/1000000000) (ψ := -4681/8000) 179 73
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t13 : ((703686873/5000000000 : ℚ) : ℝ) ≤ stT179 13 := by
  have hc : ((126859/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((703686873/5000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((126859/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c14 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-82963/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1085933/2500000) (δ := 457/50000000) (ψ := -4681/8000) 179 75
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t14 : ((-55448701911/1250000000000 : ℚ) : ℝ) ≤ stT179 14 := by
  have hc : ((-20747/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55448701911/1250000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-20747/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c15 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((12481/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237633/625000) (δ := 4527/500000000) (ψ := -4681/8000) 179 77
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t15 : ((16096758689/1250000000000 : ℚ) : ℝ) ≤ stT179 15 := by
  have hc : ((24937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16096758689/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((24937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c16 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((874267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63359/500000) (δ := 8969/1000000000) (ψ := -4681/8000) 179 79
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t16 : ((874217/4000000 : ℚ) : ℝ) ≤ stT179 16 := by
  have hc : ((874217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((874217/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((874217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c17 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((14207/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509619/5000000) (δ := 8983/1000000000) (ψ := -4681/8000) 179 81
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t17 : ((1722609099/20000000000 : ℚ) : ℝ) ≤ stT179 17 := by
  have hc : ((2841/8000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1722609099/20000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((2841/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c18 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-57539/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6851183/10000000) (δ := 909/100000000) (ψ := -4681/8000) 179 82
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t18 : ((-1085024896751/5000000000000 : ℚ) : ℝ) ≤ stT179 18 := by
  have hc : ((-460337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1085024896751/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-460337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c19 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((989087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46209/1250000) (δ := 4499/500000000) (ψ := -4681/8000) 179 84
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t19 : ((2269006156809/10000000000000 : ℚ) : ℝ) ≤ stT179 19 := by
  have hc : ((989037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2269006156809/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((989037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c20 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-924473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6876117/10000000) (δ := 1139/125000000) (ψ := -4681/8000) 179 85
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t20 : ((-516824073891/2500000000000 : ℚ) : ℝ) ≤ stT179 20 := by
  have hc : ((-924523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-516824073891/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-924523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c21 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((469141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541239/2000000) (δ := 4563/500000000) (ψ := -4681/8000) 179 87
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t21 : ((511820030099/5000000000000 : ℚ) : ℝ) ≤ stT179 21 := by
  have hc : ((469091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((511820030099/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((469091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c22 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((572359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2403541/10000000) (δ := 907/100000000) (ψ := -4681/8000) 179 88
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t22 : ((1220166794163/10000000000000 : ℚ) : ℝ) ≤ stT179 22 := by
  have hc : ((572309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1220166794163/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((572309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c23 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-874453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6587759/10000000) (δ := 457/50000000) (ψ := -4681/8000) 179 89
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t23 : ((-364693111587/2000000000000 : ℚ) : ℝ) ≤ stT179 23 := by
  have hc : ((-874503/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364693111587/2000000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-874503/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c24 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-337993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5782747/10000000) (δ := 1791/200000000) (ψ := -4681/8000) 179 91
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t24 : ((-172494134589/1250000000000 : ℚ) : ℝ) ≤ stT179 24 := by
  have hc : ((-169009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172494134589/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-169009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c25 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((277941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -644573/2000000) (δ := 4531/500000000) (ψ := -4681/8000) 179 92
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t25 : ((277891/5000000 : ℚ) : ℝ) ≤ stT179 25 := by
  have hc : ((277891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277891/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((277891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c26 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((851569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275913/2000000) (δ := 9069/1000000000) (ψ := -4681/8000) 179 93
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t26 : ((1669965853559/10000000000000 : ℚ) : ℝ) ≤ stT179 26 := by
  have hc : ((851519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1669965853559/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((851519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c27 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((498421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24843/1250000) (δ := 2269/250000000) (ψ := -4681/8000) 179 94
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t27 : ((479581551/2500000000 : ℚ) : ℝ) ≤ stT179 27 := by
  have hc : ((124599/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((479581551/2500000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((124599/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c28 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((197839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183919/5000000) (δ := 9019/1000000000) (ψ := -4681/8000) 179 95
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t28 : ((186930798219/1000000000000 : ℚ) : ℝ) ≤ stT179 28 := by
  have hc : ((197829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186930798219/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((197829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c29 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((123683/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11351/312500) (δ := 9091/1000000000) (ψ := -4681/8000) 179 96
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t29 : ((918647647771/5000000000000 : ℚ) : ℝ) ≤ stT179 29 := by
  have hc : ((494707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((918647647771/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((494707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c30 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((62349/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17381/1000000) (δ := 4549/500000000) (ψ := -4681/8000) 179 97
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t30 : ((910619361347/5000000000000 : ℚ) : ℝ) ≤ stT179 30 := by
  have hc : ((498767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((910619361347/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((498767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c31 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((442729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1208293/10000000) (δ := 1821/200000000) (ψ := -4681/8000) 179 98
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t31 : ((49694990457/312500000000 : ℚ) : ℝ) ≤ stT179 31 := by
  have hc : ((27669/31250 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49694990457/312500000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((27669/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c32 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((117063/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2708713/10000000) (δ := 1139/125000000) (ψ := -4681/8000) 179 99
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t32 : ((206917894183/2500000000000 : ℚ) : ℝ) ≤ stT179 32 := by
  have hc : ((234101/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206917894183/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((234101/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c33 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-283803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2323193/5000000) (δ := 2271/250000000) (ψ := -4681/8000) 179 100
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t33 : ((-494124773781/10000000000000 : ℚ) : ℝ) ≤ stT179 33 := by
  have hc : ((-283853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-494124773781/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-283853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c34 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-14712/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6995131/10000000) (δ := 9127/1000000000) (ψ := -4681/8000) 179 101
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t34 : ((-403715421837/2500000000000 : ℚ) : ℝ) ≤ stT179 34 := by
  have hc : ((-470809/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-403715421837/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-470809/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c35 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-731087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239071/400000) (δ := 9027/1000000000) (ψ := -4681/8000) 179 101
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t35 : ((-1235847451333/10000000000000 : ℚ) : ℝ) ≤ stT179 35 := by
  have hc : ((-731137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1235847451333/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-731137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c36 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((204191/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2875289/10000000) (δ := 9069/1000000000) (ψ := -4681/8000) 179 102
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t36 : ((85069132639/1250000000000 : ℚ) : ℝ) ≤ stT179 36 := by
  have hc : ((102083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85069132639/1250000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((102083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c37 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((486987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -571621/10000000) (δ := 9141/1000000000) (ψ := -4681/8000) 179 103
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t37 : ((400280085709/2500000000000 : ℚ) : ℝ) ≤ stT179 37 := by
  have hc : ((243481/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400280085709/2500000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((243481/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c38 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-166649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -869113/2000000) (δ := 1131/125000000) (ψ := -4681/8000) 179 104
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t38 : ((-54084323657/2000000000000 : ℚ) : ℝ) ≤ stT179 38 := by
  have hc : ((-166699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54084323657/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-166699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c39 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-48681/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7278471/10000000) (δ := 1791/200000000) (ψ := -4681/8000) 179 104
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t39 : ((-77956012247/500000000000 : ℚ) : ℝ) ≤ stT179 39 := by
  have hc : ((-97367/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77956012247/500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-97367/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c40 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((199629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2900223/10000000) (δ := 1131/125000000) (ψ := -4681/8000) 179 105
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t40 : ((39450183669/625000000000 : ℚ) : ℝ) ≤ stT179 40 := by
  have hc : ((49901/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39450183669/625000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((49901/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c41 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((190707/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -878901/5000000) (δ := 457/50000000) (ψ := -4681/8000) 179 106
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t41 : ((595629312693/5000000000000 : ℚ) : ℝ) ≤ stT179 41 := by
  have hc : ((381389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((595629312693/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((381389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c42 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-892131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6682089/10000000) (δ := 9033/1000000000) (ψ := -4681/8000) 179 107
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t42 : ((-688332808577/5000000000000 : ℚ) : ℝ) ≤ stT179 42 := by
  have hc : ((-892181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-688332808577/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-892181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c43 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((31667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 384781/1000000) (δ := 897/100000000) (ψ := -4681/8000) 179 107
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t43 : ((9643090149/2000000000000 : ℚ) : ℝ) ≤ stT179 43 := by
  have hc : ((31617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9643090149/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((31617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c44 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((808651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12284/78125) (δ := 8977/1000000000) (ψ := -4681/8000) 179 108
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t44 : ((304752822289/2500000000000 : ℚ) : ℝ) ≤ stT179 44 := by
  have hc : ((808601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((304752822289/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((808601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c45 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-968391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7223737/10000000) (δ := 2271/250000000) (ψ := -4681/8000) 179 109
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t45 : ((-180458327499/1250000000000 : ℚ) : ℝ) ≤ stT179 45 := by
  have hc : ((-968441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180458327499/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-968441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c46 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((502137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130591/500000) (δ := 9119/1000000000) (ψ := -4681/8000) 179 109
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t46 : ((740286612453/10000000000000 : ℚ) : ℝ) ≤ stT179 46 := by
  have hc : ((502087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((740286612453/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((502087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c47 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((45241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1736037/5000000) (δ := 1139/125000000) (ψ := -4681/8000) 179 110
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t47 : ((131945012593/5000000000000 : ℚ) : ℝ) ≤ stT179 47 := by
  have hc : ((90457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131945012593/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((90457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c48 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-723551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5949323/10000000) (δ := 8991/1000000000) (ψ := -4681/8000) 179 110
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t48 : ((-65276769811/625000000000 : ℚ) : ℝ) ≤ stT179 48 := by
  have hc : ((-723601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65276769811/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-723601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c49 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((488741/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -132887/2500000) (δ := 4549/500000000) (ψ := -4681/8000) 179 111
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t49 : ((174541376209/1250000000000 : ℚ) : ℝ) ≤ stT179 49 := by
  have hc : ((122179/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174541376209/1250000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((122179/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c50 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-965851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7198759/10000000) (δ := 9097/1000000000) (ψ := -4681/8000) 179 112
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t50 : ((-682995358407/5000000000000 : ℚ) : ℝ) ≤ stT179 50 := by
  have hc : ((-965901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-682995358407/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-965901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c51 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((786817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332581/2000000) (δ := 4503/500000000) (ψ := -4681/8000) 179 112
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t51 : ((27542352369/250000000000 : ℚ) : ℝ) ≤ stT179 51 := by
  have hc : ((786767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27542352369/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((786767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c52 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-540799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5355459/10000000) (δ := 909/100000000) (ψ := -4681/8000) 179 113
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t52 : ((-750022891599/10000000000000 : ℚ) : ℝ) ≤ stT179 52 := by
  have hc : ((-540849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750022891599/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-540849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c53 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((298721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3168611/10000000) (δ := 9013/1000000000) (ψ := -4681/8000) 179 113
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t53 : ((82051195791/2000000000000 : ℚ) : ℝ) ≤ stT179 53 := by
  have hc : ((298671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82051195791/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((298671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c54 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-98897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2087319/5000000) (δ := 9083/1000000000) (ψ := -4681/8000) 179 114
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t54 : ((-33662462029/2500000000000 : ℚ) : ℝ) ≤ stT179 54 := by
  have hc : ((-98947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33662462029/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-98947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c55 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-2739/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 807317/2000000) (δ := 57/6250000) (ψ := -4681/8000) 179 114
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t55 : ((-73949627/12500000000 : ℚ) : ℝ) ≤ stT179 55 := by
  have hc : ((-21937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73949627/12500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-21937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c56 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((127211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36081/100000) (δ := 561/62500000) (ψ := -4681/8000) 179 115
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t56 : ((84963003633/5000000000000 : ℚ) : ℝ) ≤ stT179 56 := by
  have hc : ((127161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84963003633/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((127161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c57 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-76791/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4312471/10000000) (δ := 561/62500000) (ψ := -4681/8000) 179 115
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t57 : ((-6359082933/312500000000 : ℚ) : ℝ) ≤ stT179 57 := by
  have hc : ((-4801/31250 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6359082933/312500000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-4801/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c58 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((125401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1806331/5000000) (δ := 9069/1000000000) (ψ := -4681/8000) 179 116
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t58 : ((20574235683/1250000000000 : ℚ) : ℝ) ≤ stT179 58 := by
  have hc : ((125351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20574235683/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((125351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c59 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-22011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2018541/5000000) (δ := 9069/1000000000) (ψ := -4681/8000) 179 116
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t59 : ((-717211201/125000000000 : ℚ) : ℝ) ≤ stT179 59 := by
  have hc : ((-5509/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-717211201/125000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-5509/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c60 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-88967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -518713/1250000) (δ := 9061/1000000000) (ψ := -4681/8000) 179 117
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t60 : ((-22984100383/2000000000000 : ℚ) : ℝ) ≤ stT179 60 := by
  have hc : ((-89017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22984100383/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-89017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c61 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((134297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1623579/5000000) (δ := 8961/1000000000) (ψ := -4681/8000) 179 117
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t61 : ((83944127/2441406250 : ℚ) : ℝ) ≤ stT179 61 := by
  have hc : ((4196/15625 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83944127/2441406250 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((4196/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c62 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-96393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5184231/10000000) (δ := 9149/1000000000) (ψ := -4681/8000) 179 118
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t62 : ((-61216001403/1000000000000 : ℚ) : ℝ) ≤ stT179 62 := by
  have hc : ((-96403/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61216001403/1000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-96403/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c63 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((87947/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 493987/2500000) (δ := 9149/1000000000) (ψ := -4681/8000) 179 118
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t63 : ((443179520203/5000000000000 : ℚ) : ℝ) ≤ stT179 63 := by
  have hc : ((351763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((443179520203/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((351763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c64 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-892593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1671163/2500000) (δ := 9147/1000000000) (ψ := -4681/8000) 179 119
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t64 : ((-1115804642643/10000000000000 : ℚ) : ℝ) ≤ stT179 64 := by
  have hc : ((-892643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1115804642643/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-892643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c65 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((62179/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126739/5000000) (δ := 2239/250000000) (ψ := -4681/8000) 179 119
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t65 : ((616957280229/5000000000000 : ℚ) : ℝ) ≤ stT179 65 := by
  have hc : ((497407/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((616957280229/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((497407/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c66 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-238287/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1771421/2500000) (δ := 9047/1000000000) (ψ := -4681/8000) 179 119
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t66 : ((-117330571617/1000000000000 : ℚ) : ℝ) ≤ stT179 66 := by
  have hc : ((-476599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117330571617/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-476599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c67 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((181703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1892819/10000000) (δ := 113/12500000) (ψ := -4681/8000) 179 120
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t67 : ((221970193707/2500000000000 : ℚ) : ℝ) ≤ stT179 67 := by
  have hc : ((363381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((221970193707/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((363381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c68 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-318341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2368469/5000000) (δ := 457/50000000) (ψ := -4681/8000) 179 120
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t68 : ((-386106079489/10000000000000 : ℚ) : ℝ) ≤ stT179 68 := by
  have hc : ((-318391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-386106079489/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-318391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c69 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-3172/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2219031/5000000) (δ := 9033/1000000000) (ψ := -4681/8000) 179 121
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t69 : ((-122226600411/5000000000000 : ℚ) : ℝ) ≤ stT179 69 := by
  have hc : ((-101529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122226600411/5000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-101529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c70 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((348227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2000881/10000000) (δ := 9133/1000000000) (ψ := -4681/8000) 179 121
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t70 : ((52022597507/625000000000 : ℚ) : ℝ) ≤ stT179 70 := by
  have hc : ((174101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52022597507/625000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((174101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c71 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-980501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7359473/10000000) (δ := 9077/1000000000) (ψ := -4681/8000) 179 122
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t71 : ((-581850138441/5000000000000 : ℚ) : ℝ) ≤ stT179 71 := by
  have hc : ((-980551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-581850138441/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-980551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c72 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((904649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -275151/2500000) (δ := 8977/1000000000) (ψ := -4681/8000) 179 122
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t72 : ((1066079872089/10000000000000 : ℚ) : ℝ) ≤ stT179 72 := by
  have hc : ((904599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1066079872089/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((904599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c73 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-221061/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2535949/5000000) (δ := 9077/1000000000) (ψ := -4681/8000) 179 122
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t73 : ((-32345213429/625000000000 : ℚ) : ℝ) ≤ stT179 73 := by
  have hc : ((-110543/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32345213429/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-110543/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c74 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-122843/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113689/250000) (δ := 4559/500000000) (ψ := -4681/8000) 179 123
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t74 : ((-35707806009/1250000000000 : ℚ) : ℝ) ≤ stT179 74 := by
  have hc : ((-30717/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35707806009/1250000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-30717/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c75 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((834423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 729639/5000000) (δ := 1817/200000000) (ψ := -4681/8000) 179 123
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t75 : ((9634505031/100000000000 : ℚ) : ℝ) ≤ stT179 75 := by
  have hc : ((834373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9634505031/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((834373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c76 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-122821/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1477301/2000000) (δ := 1817/200000000) (ψ := -4681/8000) 179 123
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t76 : ((-563570236411/5000000000000 : ℚ) : ℝ) ≤ stT179 76 := by
  have hc : ((-491309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-563570236411/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-491309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c77 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((109959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1235847/5000000) (δ := 9011/1000000000) (ψ := -4681/8000) 179 124
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t77 : ((25059686029/400000000000 : ℚ) : ℝ) ≤ stT179 77 := by
  have hc : ((109949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25059686029/400000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((109949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c78 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((30897/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1651289/5000000) (δ := 2273/250000000) (ψ := -4681/8000) 179 124
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t78 : ((139907542951/5000000000000 : ℚ) : ℝ) ≤ stT179 78 := by
  have hc : ((123563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139907542951/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((123563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c79 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-896177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6704683/10000000) (δ := 8999/1000000000) (ψ := -4681/8000) 179 125
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t79 : ((-31510445093/312500000000 : ℚ) : ℝ) ≤ stT179 79 := by
  have hc : ((-896227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31510445093/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-896227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c80 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((454427/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -107567/1000000) (δ := 8999/1000000000) (ψ := -4681/8000) 179 125
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t80 : ((254018215633/2500000000000 : ℚ) : ℝ) ≤ stT179 80 := by
  have hc : ((227201/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254018215633/2500000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((227201/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c81 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-22073/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4483399/10000000) (δ := 9099/1000000000) (ψ := -4681/8000) 179 125
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t81 : ((-1533195671/62500000000 : ℚ) : ℝ) ≤ stT179 81 := by
  have hc : ((-11039/50000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1533195671/62500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-11039/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c82 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-330699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1146739/2000000) (δ := 8997/1000000000) (ψ := -4681/8000) 179 126
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t82 : ((-22826487799/312500000000 : ℚ) : ℝ) ≤ stT179 82 := by
  have hc : ((-82681/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22826487799/312500000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-82681/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c83 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((992353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38671/1250000) (δ := 4553/500000000) (ψ := -4681/8000) 179 126
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t83 : ((544596724763/5000000000000 : ℚ) : ℝ) ≤ stT179 83 := by
  have hc : ((992303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((544596724763/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((992303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c84 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-217117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5049959/10000000) (δ := 9003/500000000) (ψ := -4681/8000) 179 126
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t84 : ((-11846073239/250000000000 : ℚ) : ℝ) ≤ stT179 84 := by
  have hc : ((-108571/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11846073239/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-108571/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c85 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-135757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670261/1250000) (δ := 9013/1000000000) (ψ := -4681/8000) 179 127
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t85 : ((-294525590967/5000000000000 : ℚ) : ℝ) ≤ stT179 85 := by
  have hc : ((-271539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294525590967/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-271539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c86 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((998687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1001/78125) (δ := 9013/1000000000) (ψ := -4681/8000) 179 127
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t86 : ((1076857240299/10000000000000 : ℚ) : ℝ) ≤ stT179 86 := by
  have hc : ((998637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1076857240299/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((998637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c87 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-432581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40363/80000) (δ := 9113/1000000000) (ψ := -4681/8000) 179 127
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t87 : ((-463829319303/10000000000000 : ℚ) : ℝ) ≤ stT179 87 := by
  have hc : ((-432631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463829319303/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-432631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c88 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-603993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1109649/2000000) (δ := 57/6250000) (ψ := -4681/8000) 179 128
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t88 : ((-160978063543/2500000000000 : ℚ) : ℝ) ≤ stT179 88 := by
  have hc : ((-604043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160978063543/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-604043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c89 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((980719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -491719/10000000) (δ := 451/50000000) (ψ := -4681/8000) 179 128
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t89 : ((1039506197993/10000000000000 : ℚ) : ℝ) ≤ stT179 89 := by
  have hc : ((980669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1039506197993/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((980669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c90 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-230447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4508333/10000000) (δ := 57/6250000) (ψ := -4681/8000) 179 128
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t90 : ((-242965274221/10000000000000 : ℚ) : ℝ) ≤ stT179 90 := by
  have hc : ((-230497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242965274221/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-230497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c91 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-802297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6254823/10000000) (δ := 719/40000000) (ψ := -4681/8000) 179 129
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t91 : ((-168217664979/2000000000000 : ℚ) : ℝ) ≤ stT179 91 := by
  have hc : ((-802347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168217664979/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-802347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c92 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((854801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1364073/10000000) (δ := 359/40000000) (ψ := -4681/8000) 179 129
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t92 : ((222784864893/2500000000000 : ℚ) : ℝ) ≤ stT179 92 := by
  have hc : ((854751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222784864893/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((854751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c93 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((180283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 694761/2000000) (δ := 2257/250000000) (ψ := -4681/8000) 179 129
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t93 : ((186892789583/10000000000000 : ℚ) : ℝ) ≤ stT179 93 := by
  have hc : ((180233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186892789583/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((180233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c94 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-246711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1862003/2500000) (δ := 2267/250000000) (ψ := -4681/8000) 179 130
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t94 : ((-254476045817/2500000000000 : ℚ) : ℝ) ≤ stT179 94 := by
  have hc : ((-493447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254476045817/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-493447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c95 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((93381/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1356261/5000000) (δ := 1121/125000000) (ψ := -4681/8000) 179 130
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t95 : ((47898295919/1000000000000 : ℚ) : ℝ) ≤ stT179 95 := by
  have hc : ((93371/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47898295919/1000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((93371/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c96 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((44019/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 394677/2000000) (δ := 1807/200000000) (ψ := -4681/8000) 179 130
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t96 : ((17969392937/250000000000 : ℚ) : ℝ) ≤ stT179 96 := by
  have hc : ((352127/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17969392937/250000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((352127/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c97 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-7031/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3305369/5000000) (δ := 1807/200000000) (ψ := -4681/8000) 179 130
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t97 : ((-35696554479/400000000000 : ℚ) : ℝ) ≤ stT179 97 := by
  have hc : ((-35157/40000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35696554479/400000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-35157/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c98 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-2301/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2253721/5000000) (δ := 9061/1000000000) (ψ := -4681/8000) 179 131
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t98 : ((-4649734259/200000000000 : ℚ) : ℝ) ≤ stT179 98 := by
  have hc : ((-4603/20000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4649734259/200000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-4603/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c99 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((499949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35757/10000000) (δ := 9061/1000000000) (ψ := -4681/8000) 179 131
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t99 : ((125610529297/1250000000000 : ℚ) : ℝ) ≤ stT179 99 := by
  have hc : ((124981/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125610529297/1250000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((124981/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c100 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-12007/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4533267/10000000) (δ := 4571/500000000) (ψ := -4681/8000) 179 131
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t100 : ((-24019/1000000 : ℚ) : ℝ) ≤ stT179 100 := by
  have hc : ((-24019/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24019/1000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-24019/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c101 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-89921/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6721893/10000000) (δ := 4527/500000000) (ψ := -4681/8000) 179 132
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t101 : ((-22369946797/250000000000 : ℚ) : ℝ) ≤ stT179 101 := by
  have hc : ((-44963/50000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22369946797/250000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-44963/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c102 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((601679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -578247/2500000) (δ := 9149/1000000000) (ψ := -4681/8000) 179 132
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t102 : ((595701149463/10000000000000 : ℚ) : ℝ) ≤ stT179 102 := by
  have hc : ((601629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((595701149463/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((601629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c103 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((681383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1026433/5000000) (δ := 4527/500000000) (ψ := -4681/8000) 179 132
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t103 : ((671337163557/10000000000000 : ℚ) : ℝ) ≤ stT179 103 := by
  have hc : ((681333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((671337163557/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((681333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c104 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-830403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6376567/10000000) (δ := 9149/1000000000) (ψ := -4681/8000) 179 132
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t104 : ((-814326433193/10000000000000 : ℚ) : ℝ) ≤ stT179 104 := by
  have hc : ((-830453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-814326433193/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-830453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c105 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-86781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2524523/5000000) (δ := 9147/1000000000) (ψ := -4681/8000) 179 133
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t105 : ((-84699423691/2000000000000 : ℚ) : ℝ) ≤ stT179 105 := by
  have hc : ((-86791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84699423691/2000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-86791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c106 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((948309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -807327/10000000) (δ := 283/31250000) (ψ := -4681/8000) 179 133
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t106 : ((184205948563/2000000000000 : ℚ) : ℝ) ≤ stT179 106 := by
  have hc : ((948259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184205948563/2000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((948259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c107 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((211347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212163/625000) (δ := 9047/1000000000) (ψ := -4681/8000) 179 133
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t107 : ((12766776037/625000000000 : ℚ) : ℝ) ≤ stT179 107 := by
  have hc : ((211297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12766776037/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((211297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c108 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-992973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 944679/1250000) (δ := 9047/1000000000) (ψ := -4681/8000) 179 133
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t108 : ((-955537374773/10000000000000 : ℚ) : ℝ) ≤ stT179 108 := by
  have hc : ((-993023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-955537374773/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-993023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c109 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-19817/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4026103/10000000) (δ := 9139/1000000000) (ψ := -4681/8000) 179 134
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t109 : ((-9502601667/2500000000000 : ℚ) : ℝ) ≤ stT179 109 := by
  have hc : ((-9921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9502601667/2500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-9921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c110 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((199941/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60691/10000000) (δ := 9039/1000000000) (ψ := -4681/8000) 179 134
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t110 : ((95313305561/1000000000000 : ℚ) : ℝ) ≤ stT179 110 := by
  have hc : ((199931/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95313305561/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((199931/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c111 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-36673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4110521/10000000) (δ := 9139/1000000000) (ψ := -4681/8000) 179 134
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t111 : ((-8708050071/1250000000000 : ℚ) : ℝ) ≤ stT179 111 := by
  have hc : ((-18349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8708050071/1250000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-18349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c112 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-497087/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7583993/10000000) (δ := 9071/1000000000) (ψ := -4681/8000) 179 135
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t112 : ((-3669742923/39062500000 : ℚ) : ℝ) ≤ stT179 112 := by
  have hc : ((-62139/62500 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3669742923/39062500000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-62139/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c113 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((63989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1803083/5000000) (δ := 1129/125000000) (ψ := -4681/8000) 179 135
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t113 : ((188038169/15625000000 : ℚ) : ℝ) ≤ stT179 113 := by
  have hc : ((15991/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188038169/15625000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((15991/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c114 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((990951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 168289/5000000) (δ := 9071/1000000000) (ψ := -4681/8000) 179 135
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t114 : ((185612602617/2000000000000 : ℚ) : ℝ) ≤ stT179 114 := by
  have hc : ((990901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185612602617/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((990901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c115 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-15853/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1061227/2500000) (δ := 2283/250000000) (ψ := -4681/8000) 179 135
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t115 : ((-11831063937/1000000000000 : ℚ) : ℝ) ≤ stT179 115 := by
  have hc : ((-63437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11831063937/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-63437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c116 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-994371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37943/50000) (δ := 361/40000000) (ψ := -4681/8000) 179 136
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t116 : ((-923297026817/10000000000000 : ℚ) : ℝ) ≤ stT179 116 := by
  have hc : ((-994421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-923297026817/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-994421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c117 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((14359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3747349/10000000) (δ := 4539/500000000) (ψ := -4681/8000) 179 136
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t117 : ((26531301/4000000000 : ℚ) : ℝ) ≤ stT179 117 := by
  have hc : ((14349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26531301/4000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((14349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c118 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((9997/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61189/10000000) (δ := 4489/500000000) (ψ := -4681/8000) 179 136
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t118 : ((9202517991/100000000000 : ℚ) : ℝ) ≤ stT179 118 := by
  have hc : ((19993/20000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9202517991/100000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((19993/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c119 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((4471/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 239847/625000) (δ := 4489/500000000) (ψ := -4681/8000) 179 136
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t119 : ((8185654791/2500000000000 : ℚ) : ℝ) ≤ stT179 119 := by
  have hc : ((17859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8185654791/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((17859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c120 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-124263/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3791183/5000000) (δ := 361/40000000) (ψ := -4681/8000) 179 136
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t120 : ((-453767178067/5000000000000 : ℚ) : ℝ) ≤ stT179 120 := by
  have hc : ((-497077/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453767178067/5000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-497077/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c121 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-192743/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1102971/2500000) (δ := 1797/200000000) (ψ := -4681/8000) 179 137
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t121 : ((-175266381163/10000000000000 : ℚ) : ℝ) ≤ stT179 121 := by
  have hc : ((-192793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175266381163/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-192793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c122 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((119727/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145747/2000000) (δ := 1817/200000000) (ψ := -4681/8000) 179 137
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t122 : ((433560076231/5000000000000 : ℚ) : ℝ) ≤ stT179 122 := by
  have hc : ((478883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((433560076231/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((478883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c123 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((195197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2924341/10000000) (δ := 4559/500000000) (ψ := -4681/8000) 179 137
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t123 : ((43995135517/1250000000000 : ℚ) : ℝ) ≤ stT179 123 := by
  have hc : ((48793/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43995135517/1250000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((48793/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c124 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-216649/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3273919/5000000) (δ := 4559/500000000) (ψ := -4681/8000) 179 137
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t124 : ((-389135753721/5000000000000 : ℚ) : ℝ) ≤ stT179 124 := by
  have hc : ((-433323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-389135753721/5000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-433323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c125 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-152387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1113143/2000000) (δ := 2273/250000000) (ψ := -4681/8000) 179 138
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t125 : ((-68155189993/1250000000000 : ℚ) : ℝ) ≤ stT179 125 := by
  have hc : ((-304799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68155189993/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-304799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c126 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((348361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -999973/5000000) (δ := 9011/1000000000) (ψ := -4681/8000) 179 138
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t126 : ((1939513077/31250000000 : ℚ) : ℝ) ≤ stT179 126 := by
  have hc : ((21771/31250 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1939513077/31250000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((21771/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c127 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((408377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 768793/5000000) (δ := 9111/1000000000) (ψ := -4681/8000) 179 138
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t127 : ((2830887479/39062500000 : ℚ) : ℝ) ≤ stT179 127 := by
  have hc : ((12761/15625 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2830887479/39062500000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((12761/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c128 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-216659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2523709/5000000) (δ := 9111/1000000000) (ψ := -4681/8000) 179 138
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t128 : ((-11970220041/312500000000 : ℚ) : ℝ) ≤ stT179 128 := by
  have hc : ((-54171/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11970220041/312500000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-54171/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c129 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-963667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -717801/1000000) (δ := 9099/1000000000) (ψ := -4681/8000) 179 139
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t129 : ((-848505596367/10000000000000 : ℚ) : ℝ) ≤ stT179 129 := by
  have hc : ((-963717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-848505596367/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-963717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c130 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((81739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -744483/2000000) (δ := 9099/1000000000) (ψ := -4681/8000) 179 139
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t130 : ((35822995481/5000000000000 : ℚ) : ℝ) ≤ stT179 130 := by
  have hc : ((81689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35822995481/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((81689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c131 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((993127/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -73317/2500000) (δ := 569/62500000) (ψ := -4681/8000) 179 139
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t131 : ((108456918401/1250000000000 : ℚ) : ℝ) ≤ stT179 131 := by
  have hc : ((993077/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108456918401/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((993077/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c132 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((32109/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3109791/10000000) (δ := 8999/1000000000) (ψ := -4681/8000) 179 139
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t132 : ((873216761/31250000000 : ℚ) : ℝ) ≤ stT179 132 := by
  have hc : ((4013/12500 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((873216761/31250000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((4013/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c133 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-85423/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6487163/10000000) (δ := 8999/1000000000) (ψ := -4681/8000) 179 139
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t133 : ((-1851886827/25000000000 : ℚ) : ℝ) ≤ stT179 133 := by
  have hc : ((-21357/25000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1851886827/25000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-21357/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c134 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-10952/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1173747/2000000) (δ := 1131/62500000) (ψ := -4681/8000) 179 140
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t134 : ((-302776581941/5000000000000 : ℚ) : ℝ) ≤ stT179 134 := by
  have hc : ((-350489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-302776581941/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-350489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c135 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((131557/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1270797/5000000) (δ := 9107/1000000000) (ψ := -4681/8000) 179 140
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t135 : ((113215352459/2500000000000 : ℚ) : ℝ) ≤ stT179 135 := by
  have hc : ((263089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113215352459/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((263089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c136 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((954027/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 761/10000) (δ := 1137/125000000) (ψ := -4681/8000) 179 140
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t136 : ((204506911421/2500000000000 : ℚ) : ℝ) ≤ stT179 136 := by
  have hc : ((953977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204506911421/2500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((953977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c137 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-44961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403943/1000000) (δ := 2249/250000000) (ψ := -4681/8000) 179 140
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t137 : ((-19227753969/5000000000000 : ℚ) : ℝ) ≤ stT179 137 := by
  have hc : ((-45011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19227753969/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-45011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c138 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-195003/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7293963/10000000) (δ := 1137/125000000) (ψ := -4681/8000) 179 140
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t138 : ((-166006181341/2000000000000 : ℚ) : ℝ) ≤ stT179 138 := by
  have hc : ((-195013/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166006181341/2000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-195013/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c139 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-15047/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1295729/2500000) (δ := 9089/1000000000) (ψ := -4681/8000) 179 141
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t139 : ((-204224402853/5000000000000 : ℚ) : ℝ) ≤ stT179 139 := by
  have hc : ((-240777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-204224402853/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-240777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c140 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((351921/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493753/2500000) (δ := 8989/1000000000) (ψ := -4681/8000) 179 141
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t140 : ((18587894499/312500000000 : ℚ) : ℝ) ≤ stT179 140 := by
  have hc : ((43987/62500 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18587894499/312500000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((43987/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c141 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((55321/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48401/400000) (δ := 4557/500000000) (ψ := -4681/8000) 179 141
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t141 : ((372688029993/5000000000000 : ℚ) : ℝ) ≤ stT179 141 := by
  have hc : ((442543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372688029993/5000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((442543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c142 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-1773/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4372597/10000000) (δ := 4557/500000000) (ψ := -4681/8000) 179 141
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t142 : ((-1488289277/100000000000 : ℚ) : ℝ) ≤ stT179 142 := by
  have hc : ((-3547/20000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1488289277/100000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-3547/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c143 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-990711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7512973/10000000) (δ := 4557/500000000) (ψ := -4681/8000) 179 141
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t143 : ((-828516950923/10000000000000 : ℚ) : ℝ) ≤ stT179 143 := by
  have hc : ((-990761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-828516950923/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-990761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c144 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-443787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2538271/5000000) (δ := 9021/1000000000) (ψ := -4681/8000) 179 142
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t144 : ((-184932231279/5000000000000 : ℚ) : ℝ) ≤ stT179 144 := by
  have hc : ((-443837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-184932231279/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-443837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c145 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((175633/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -989809/5000000) (δ := 9121/1000000000) (ψ := -4681/8000) 179 142
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t145 : ((145844746707/2500000000000 : ℚ) : ℝ) ≤ stT179 145 := by
  have hc : ((351241/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145844746707/2500000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((351241/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c146 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((905431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 274001/2500000) (δ := 4541/500000000) (ψ := -4681/8000) 179 142
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t146 : ((149859568501/2000000000000 : ℚ) : ℝ) ≤ stT179 146 := by
  have hc : ((905381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149859568501/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((905381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c147 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-44661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 830119/2000000) (δ := 9121/1000000000) (ψ := -4681/8000) 179 142
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t147 : ((-18428215941/2500000000000 : ℚ) : ℝ) ≤ stT179 147 := by
  have hc : ((-22343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18428215941/2500000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-22343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c148 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-482179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 718451/1000000) (δ := 4541/500000000) (ψ := -4681/8000) 179 142
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t148 : ((-19818463849/250000000000 : ℚ) : ℝ) ≤ stT179 148 := by
  have hc : ((-120551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19818463849/250000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-120551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c149 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-18491/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5509943/10000000) (δ := 2257/250000000) (ψ := -4681/8000) 179 143
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t149 : ((-7574849481/156250000000 : ℚ) : ℝ) ≤ stT179 149 := by
  have hc : ((-295881/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7574849481/156250000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-295881/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c150 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((534683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125833/500000) (δ := 1141/125000000) (ψ := -4681/8000) 179 143
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t150 : ((27282856623/625000000000 : ℚ) : ℝ) ≤ stT179 150 := by
  have hc : ((534633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27282856623/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((534633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c151 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((983353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228399/5000000) (δ := 359/40000000) (ψ := -4681/8000) 179 143
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t151 : ((200050045441/2500000000000 : ℚ) : ℝ) ≤ stT179 151 := by
  have hc : ((983303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((200050045441/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((983303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c152 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((102543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3410611/10000000) (δ := 363/40000000) (ψ := -4681/8000) 179 143
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t152 : ((41576533713/2500000000000 : ℚ) : ℝ) ≤ stT179 152 := by
  have hc : ((51259/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41576533713/2500000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((51259/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c153 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-823313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 793131/1250000) (δ := 2257/250000000) (ψ := -4681/8000) 179 143
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t153 : ((-665650287439/10000000000000 : ℚ) : ℝ) ≤ stT179 153 := by
  have hc : ((-823363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-665650287439/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-823363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c154 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-422947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6447587/10000000) (δ := 1807/200000000) (ψ := -4681/8000) 179 144
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t154 : ((-85210141489/1250000000000 : ℚ) : ℝ) ≤ stT179 154 := by
  have hc : ((-105743/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85210141489/1250000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-105743/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c155 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((149773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3551143/10000000) (δ := 1827/200000000) (ψ := -4681/8000) 179 144
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t155 : ((120260358337/10000000000000 : ℚ) : ℝ) ≤ stT179 155 := by
  have hc : ((149723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120260358337/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((149723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c156 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((19279/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -168329/2500000) (δ := 2267/250000000) (ψ := -4681/8000) 179 144
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t156 : ((12058389/156250000 : ℚ) : ℝ) ≤ stT179 156 := by
  have hc : ((9639/10000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12058389/156250000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((9639/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c157 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((32071/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54653/250000) (δ := 1807/200000000) (ψ := -4681/8000) 179 144
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t157 : ((25593420891/500000000000 : ℚ) : ℝ) ≤ stT179 157 := by
  have hc : ((64137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25593420891/500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((64137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c158 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-426083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5027387/10000000) (δ := 1807/200000000) (ψ := -4681/8000) 179 144
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t158 : ((-169506758607/5000000000000 : ℚ) : ℝ) ≤ stT179 158 := by
  have hc : ((-426133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169506758607/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-426133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c159 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3925377/5000000) (δ := 1807/200000000) (ψ := -4681/8000) 179 144
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t159 : ((-198272714887/2500000000000 : ℚ) : ℝ) ≤ stT179 159 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198272714887/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c160 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-434811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5051563/10000000) (δ := 9143/1000000000) (ψ := -4681/8000) 179 145
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t160 : ((-34378806077/1000000000000 : ℚ) : ℝ) ≤ stT179 160 := by
  have hc : ((-434861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34378806077/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-434861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c161 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((308699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -452683/2000000) (δ := 453/50000000) (ψ := -4681/8000) 179 145
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t161 : ((12163453307/250000000000 : ℚ) : ℝ) ≤ stT179 161 := by
  have hc : ((154337/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12163453307/250000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((154337/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c162 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((489733/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101501/2000000) (δ := 453/50000000) (ψ := -4681/8000) 179 145
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t162 : ((48093855399/625000000000 : ℚ) : ℝ) ≤ stT179 162 := by
  have hc : ((122427/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48093855399/625000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((122427/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c163 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((263111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50959/156250) (δ := 9143/1000000000) (ψ := -4681/8000) 179 145
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t163 : ((10302257943/500000000000 : ℚ) : ℝ) ≤ stT179 163 := by
  have hc : ((263061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10302257943/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((263061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c164 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-147391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47987/80000) (δ := 7/781250) (ψ := -4681/8000) 179 145
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t164 : ((-115100871469/2000000000000 : ℚ) : ℝ) ≤ stT179 164 := by
  have hc : ((-147401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115100871469/2000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-147401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c165 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-940771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1747309/2500000) (δ := 9053/1000000000) (ψ := -4681/8000) 179 146
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t165 : ((-732428207679/10000000000000 : ℚ) : ℝ) ≤ stT179 165 := by
  have hc : ((-940821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-732428207679/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-940821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c166 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-35709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2142653/5000000) (δ := 183/20000000) (ψ := -4681/8000) 179 146
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t166 : ((-55450555893/5000000000000 : ℚ) : ℝ) ≤ stT179 166 := by
  have hc : ((-71443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55450555893/5000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-71443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c167 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((401337/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1597577/10000000) (δ := 9053/1000000000) (ψ := -4681/8000) 179 146
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t167 : ((9704514243/156250000000 : ℚ) : ℝ) ≤ stT179 167 := by
  have hc : ((12541/15625 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9704514243/156250000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((12541/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c168 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((7273/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1074043/10000000) (δ := 8953/1000000000) (ψ := -4681/8000) 179 146
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t168 : ((7013659077/100000000000 : ℚ) : ℝ) ≤ stT179 168 := by
  have hc : ((36363/40000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7013659077/100000000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((36363/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c169 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((4923/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1864933/5000000) (δ := 8953/1000000000) (ψ := -4681/8000) 179 146
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t169 : ((3027612357/500000000000 : ℚ) : ℝ) ≤ stT179 169 := by
  have hc : ((39359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3027612357/500000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((39359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c170 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-207233/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3184991/5000000) (δ := 181/20000000) (ψ := -4681/8000) 179 146
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t170 : ((-63580017963/1000000000000 : ℚ) : ℝ) ≤ stT179 170 := by
  have hc : ((-414491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63580017963/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-414491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c171 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-89771/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6713349/10000000) (δ := 9057/1000000000) (ψ := -4681/8000) 179 147
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t171 : ((-53635549/781250000 : ℚ) : ℝ) ≤ stT179 171 := by
  have hc : ((-5611/6250 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53635549/781250000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-5611/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c172 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-70753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2052011/5000000) (δ := 4573/500000000) (ψ := -4681/8000) 179 147
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t172 : ((-53986791879/10000000000000 : ℚ) : ℝ) ≤ stT179 172 := by
  have hc : ((-70803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53986791879/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-70803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c173 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((102889/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509819/10000000) (δ := 9057/1000000000) (ψ := -4681/8000) 179 147
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t173 : ((62576169267/1000000000000 : ℚ) : ℝ) ≤ stT179 173 := by
  have hc : ((411531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62576169267/1000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((411531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c174 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((909891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267359/2500000) (δ := 4573/500000000) (ψ := -4681/8000) 179 147
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t174 : ((344874321209/5000000000000 : ℚ) : ℝ) ≤ stT179 174 := by
  have hc : ((909841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344874321209/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((909841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c175 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((58479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145357/400000) (δ := 9057/1000000000) (ψ := -4681/8000) 179 147
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t175 : ((2761688457/312500000000 : ℚ) : ℝ) ≤ stT179 175 := by
  have hc : ((29227/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2761688457/312500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((29227/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c176 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-196253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309189/500000) (δ := 9057/1000000000) (ψ := -4681/8000) 179 147
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t176 : ((-295881624649/5000000000000 : ℚ) : ℝ) ≤ stT179 176 := by
  have hc : ((-392531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295881624649/5000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-392531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c177 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-29397/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3494369/5000000) (δ := 2241/250000000) (ψ := -4681/8000) 179 148
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t177 : ((-353557460919/5000000000000 : ℚ) : ℝ) ≤ stT179 177 := by
  have hc : ((-470377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353557460919/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-470377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c178 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-214567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4467613/10000000) (δ := 9139/1000000000) (ψ := -4681/8000) 179 148
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t178 : ((-40215577311/2500000000000 : ℚ) : ℝ) ≤ stT179 178 := by
  have hc : ((-214617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40215577311/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-214617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c179 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((70793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1960583/10000000) (δ := 1133/125000000) (ψ := -4681/8000) 179 148
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t179 : ((2645471439/50000000000 : ℚ) : ℝ) ≤ stT179 179 := by
  have hc : ((17697/25000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).1
  have hw2 : ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149487/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2645471439/50000000000 : ℚ) : ℝ)
      = ((149487/2000000 : ℚ) : ℝ) * ((17697/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c180 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((488703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 532439/10000000) (δ := 9039/1000000000) (ψ := -4681/8000) 179 148
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t180 : ((36423859069/500000000000 : ℚ) : ℝ) ≤ stT179 180 := by
  have hc : ((244339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36423859069/500000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((244339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c181 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((179/500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3011679/10000000) (δ := 1133/125000000) (ψ := -4681/8000) 179 148
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t181 : ((2660620873/100000000000 : ℚ) : ℝ) ≤ stT179 181 := by
  have hc : ((7159/20000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2660620873/100000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((7159/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c182 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-581111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 219089/400000) (δ := 1133/125000000) (ψ := -4681/8000) 179 148
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t182 : ((-344628473/8000000000 : ℚ) : ℝ) ≤ stT179 182 := by
  have hc : ((-581161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344628473/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-581161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c183 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-499773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3889331/5000000) (δ := 9071/1000000000) (ψ := -4681/8000) 179 149
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t183 : ((-92365419289/1250000000000 : ℚ) : ℝ) ≤ stT179 183 := by
  have hc : ((-249899/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92365419289/1250000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-249899/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c184 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-66947/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2669983/5000000) (δ := 9071/1000000000) (ψ := -4681/8000) 179 149
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t184 : ((-19743442173/500000000000 : ℚ) : ℝ) ≤ stT179 184 := by
  have hc : ((-267813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19743442173/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-267813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c185 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((197013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -364309/1250000) (δ := 2283/250000000) (ψ := -4681/8000) 179 149
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t185 : ((18103541929/625000000000 : ℚ) : ℝ) ≤ stT179 185 := by
  have hc : ((49247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18103541929/625000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((49247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c186 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((9799/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -502089/10000000) (δ := 2283/250000000) (ψ := -4681/8000) 179 149
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t186 : ((2873841259/40000000000 : ℚ) : ℝ) ≤ stT179 186 := by
  have hc : ((19597/20000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2873841259/40000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((19597/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c187 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((14511/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 948703/5000000) (δ := 2283/250000000) (ψ := -4681/8000) 179 149
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t187 : ((132634459/2500000000 : ℚ) : ℝ) ≤ stT179 187 := by
  have hc : ((1451/2000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132634459/2500000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((1451/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c188 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-71171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2142029/5000000) (δ := 1129/125000000) (ψ := -4681/8000) 179 149
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t188 : ((-519250227/50000000000 : ℚ) : ℝ) ≤ stT179 188 := by
  have hc : ((-17799/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519250227/50000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-17799/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c189 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-887753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665809/1000000) (δ := 2283/250000000) (ψ := -4681/8000) 179 149
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t189 : ((-645781687579/10000000000000 : ℚ) : ℝ) ≤ stT179 189 := by
  have hc : ((-887803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-645781687579/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-887803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c190 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-893271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1337683/2000000) (δ := 4539/500000000) (ψ := -4681/8000) 179 150
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t190 : ((-648083839117/10000000000000 : ℚ) : ℝ) ≤ stT179 190 := by
  have hc : ((-893321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-648083839117/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-893321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c191 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-164181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4339309/10000000) (δ := 361/40000000) (ψ := -4681/8000) 179 150
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t191 : ((-4753337833/400000000000 : ℚ) : ℝ) ≤ stT179 191 := by
  have hc : ((-164231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4753337833/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-164231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c192 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((347993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2002509/10000000) (δ := 73/8000000) (ψ := -4681/8000) 179 150
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t192 : ((3923812219/78125000000 : ℚ) : ℝ) ≤ stT179 192 := by
  have hc : ((10874/15625 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3923812219/78125000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((10874/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c193 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((247927/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80541/2500000) (δ := 73/8000000) (ψ := -4681/8000) 179 150
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t193 : ((71381030327/1000000000000 : ℚ) : ℝ) ≤ stT179 193 := by
  have hc : ((495829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71381030327/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((495829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c194 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((61769/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 658711/2500000) (δ := 73/8000000) (ψ := -4681/8000) 179 150
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t194 : ((88686120929/2500000000000 : ℚ) : ℝ) ≤ stT179 194 := by
  have hc : ((247051/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88686120929/2500000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((247051/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c195 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-98149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4935621/10000000) (δ := 4489/500000000) (ψ := -4681/8000) 179 150
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t195 : ((-28117969029/1000000000000 : ℚ) : ℝ) ≤ stT179 195 := by
  have hc : ((-196323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28117969029/1000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-196323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c196 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-6053/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1806157/2500000) (δ := 361/40000000) (ψ := -4681/8000) 179 150
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t196 : ((-34590370979/500000000000 : ℚ) : ℝ) ≤ stT179 196 := by
  have hc : ((-96853/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34590370979/500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-96853/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c197 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-395239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6205963/10000000) (δ := 9017/1000000000) (ψ := -4681/8000) 179 151
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t197 : ((-137506903/2441406250 : ℚ) : ℝ) ≤ stT179 197 := by
  have hc : ((-12352/15625 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137506903/2441406250 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-12352/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c198 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-2629/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -492517/1250000) (δ := 4493/500000000) (ψ := -4681/8000) 179 151
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t198 : ((-94305909/250000000000 : ℚ) : ℝ) ≤ stT179 198 := by
  have hc : ((-1327/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94305909/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-1327/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c199 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((781151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1685721/10000000) (δ := 9117/1000000000) (ψ := -4681/8000) 179 151
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t199 : ((553707657981/10000000000000 : ℚ) : ℝ) ≤ stT179 199 := by
  have hc : ((781101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((553707657981/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((781101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c200 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((3901/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 557373/10000000) (δ := 9017/1000000000) (ψ := -4681/8000) 179 151
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t200 : ((430981107/6250000000 : ℚ) : ℝ) ≤ stT179 200 := by
  have hc : ((1219/1250 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430981107/6250000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((1219/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c201 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((219761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697331/2500000) (δ := 9017/1000000000) (ψ := -4681/8000) 179 151
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t201 : ((3874742223/125000000000 : ℚ) : ℝ) ≤ stT179 201 := by
  have hc : ((27467/62500 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3874742223/125000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((27467/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c202 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-419829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1252533/2500000) (δ := 9117/1000000000) (ψ := -4681/8000) 179 151
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t202 : ((-147713012321/5000000000000 : ℚ) : ℝ) ≤ stT179 202 := by
  have hc : ((-419879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147713012321/5000000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-419879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c203 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-48401/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3610011/5000000) (δ := 4543/500000000) (ψ := -4681/8000) 179 151
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t203 : ((-67945251441/1000000000000 : ℚ) : ℝ) ≤ stT179 203 := by
  have hc : ((-96807/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67945251441/1000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-96807/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c204 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-162073/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6288927/10000000) (δ := 911/100000000) (ψ := -4681/8000) 179 152
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t204 : ((-113480953703/2000000000000 : ℚ) : ℝ) ≤ stT179 204 := by
  have hc : ((-162083/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113480953703/2000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-162083/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c205 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-69409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1025163/2500000) (δ := 911/100000000) (ψ := -4681/8000) 179 152
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t205 : ((-48512318829/10000000000000 : ℚ) : ℝ) ≤ stT179 205 := by
  have hc : ((-69459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48512318829/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-69459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c206 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((35923/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1923027/10000000) (δ := 8993/1000000000) (ψ := -4681/8000) 179 152
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t206 : ((50053995453/1000000000000 : ℚ) : ℝ) ≤ stT179 206 := by
  have hc : ((71841/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50053995453/1000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((71841/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c207 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((995239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61009/2500000) (δ := 911/100000000) (ψ := -4681/8000) 179 152
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t207 : ((86463015509/1250000000000 : ℚ) : ℝ) ≤ stT179 207 := by
  have hc : ((995189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86463015509/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((995189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c208 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((573299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2400673/10000000) (δ := 901/100000000) (ψ := -4681/8000) 179 152
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t208 : ((3179812203/80000000000 : ℚ) : ℝ) ≤ stT179 208 := by
  have hc : ((573249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3179812203/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((573249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c209 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-245459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4546973/10000000) (δ := 9093/1000000000) (ψ := -4681/8000) 179 152
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t209 : ((-33964451587/2000000000000 : ℚ) : ℝ) ≤ stT179 209 := by
  have hc : ((-245509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33964451587/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-245509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c210 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-892299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 417689/625000) (δ := 911/100000000) (ψ := -4681/8000) 179 152
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t210 : ((-307889852517/5000000000000 : ℚ) : ℝ) ≤ stT179 210 := by
  have hc : ((-892349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-307889852517/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-892349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c211 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-92793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1379809/2000000) (δ := 91/10000000) (ψ := -4681/8000) 179 153
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t211 : ((-31942417171/500000000000 : ℚ) : ℝ) ≤ stT179 211 := by
  have hc : ((-46399/50000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31942417171/500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-46399/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c212 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-67167/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4783221/10000000) (δ := 9103/1000000000) (ψ := -4681/8000) 179 153
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t212 : ((-46137365131/2000000000000 : ℚ) : ℝ) ≤ stT179 212 := by
  have hc : ((-67177/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46137365131/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-67177/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c213 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((239653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267733/1000000) (δ := 91/10000000) (ψ := -4681/8000) 179 153
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t213 : ((10261889379/312500000000 : ℚ) : ℝ) ≤ stT179 213 := by
  have hc : ((59907/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10261889379/312500000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((59907/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c214 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((97309/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116257/2000000) (δ := 9/1000000) (ψ := -4681/8000) 179 153
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t214 : ((1662888871/25000000000 : ℚ) : ℝ) ≤ stT179 214 := by
  have hc : ((12163/12500 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1662888871/25000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((12163/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c215 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((412107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4703/31250) (δ := 9/1000000) (ψ := -4681/8000) 179 153
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t215 : ((70259362877/1250000000000 : ℚ) : ℝ) ≤ stT179 215 := by
  have hc : ((206041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70259362877/1250000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((206041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c216 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((137741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3581539/10000000) (δ := 9/1000000) (ψ := -4681/8000) 179 153
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t216 : ((93686746383/10000000000000 : ℚ) : ℝ) ≤ stT179 216 := by
  have hc : ((137691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93686746383/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((137691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c217 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-635459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5648497/10000000) (δ := 91/10000000) (ψ := -4681/8000) 179 153
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t217 : ((-86282421421/2000000000000 : ℚ) : ℝ) ≤ stT179 217 := by
  have hc : ((-635509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86282421421/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-635509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c218 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-124781/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7705967/10000000) (δ := 9103/1000000000) (ψ := -4681/8000) 179 153
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t218 : ((-169033314807/2500000000000 : ℚ) : ℝ) ≤ stT179 218 := by
  have hc : ((-499149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169033314807/2500000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-499149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c219 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-36241/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5953923/10000000) (δ := 1137/125000000) (ψ := -4681/8000) 179 154
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t219 : ((-24491110203/500000000000 : ℚ) : ℝ) ≤ stT179 219 := by
  have hc : ((-72487/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24491110203/500000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-72487/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c220 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((1179/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1957601/5000000) (δ := 9007/1000000000) (ψ := -4681/8000) 179 154
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t220 : ((1572906267/5000000000000 : ℚ) : ℝ) ≤ stT179 220 := by
  have hc : ((2333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1572906267/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((2333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c221 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((145753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18857/100000) (δ := 9007/1000000000) (ψ := -4681/8000) 179 154
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t221 : ((3063663603/62500000000 : ℚ) : ℝ) ≤ stT179 221 := by
  have hc : ((145743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3063663603/62500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((145743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c222 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((998551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134583/10000000) (δ := 1137/125000000) (ψ := -4681/8000) 179 154
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t222 : ((167537484289/2500000000000 : ℚ) : ℝ) ≤ stT179 222 := by
  have hc : ((998501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((167537484289/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((998501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c223 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((326851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2145827/10000000) (δ := 1137/125000000) (ψ := -4681/8000) 179 154
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t223 : ((109429352037/2500000000000 : ℚ) : ℝ) ≤ stT179 223 := by
  have hc : ((163413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109429352037/2500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((163413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c224 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-88319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4148077/10000000) (δ := 9107/1000000000) (ψ := -4681/8000) 179 154
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t224 : ((-29522050413/5000000000000 : ℚ) : ℝ) ≤ stT179 224 := by
  have hc : ((-88369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29522050413/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-88369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c225 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-193601/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6141421/10000000) (δ := 9107/1000000000) (ψ := -4681/8000) 179 154
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t225 : ((-258151462409/5000000000000 : ℚ) : ℝ) ≤ stT179 225 := by
  have hc : ((-387227/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258151462409/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-387227/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c226 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-994091/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3791041/5000000) (δ := 18089/1000000000) (ψ := -4681/8000) 179 155
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t226 : ((-661293645931/10000000000000 : ℚ) : ℝ) ≤ stT179 226 := by
  have hc : ((-994141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-661293645931/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-994141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c227 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-622351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5606347/10000000) (δ := 9089/1000000000) (ψ := -4681/8000) 179 155
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t227 : ((-103275620331/2500000000000 : ℚ) : ℝ) ≤ stT179 227 := by
  have hc : ((-622401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103275620331/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-622401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c228 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((1794/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -909829/2500000) (δ := 9089/1000000000) (ψ := -4681/8000) 179 155
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t228 : ((19001404939/2500000000000 : ℚ) : ℝ) ≤ stT179 228 := by
  have hc : ((57383/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19001404939/2500000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((57383/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c229 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((19559/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1680877/10000000) (δ := 9089/1000000000) (ψ := -4681/8000) 179 155
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t229 : ((25848226479/500000000000 : ℚ) : ℝ) ≤ stT179 229 := by
  have hc : ((78231/100000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25848226479/500000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((78231/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c230 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((124277/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 53803/2000000) (δ := 8989/1000000000) (ψ := -4681/8000) 179 155
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t230 : ((16388329427/250000000000 : ℚ) : ℝ) ≤ stT179 230 := by
  have hc : ((497083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16388329427/250000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((497083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c231 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((158481/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2210449/10000000) (δ := 8989/1000000000) (ψ := -4681/8000) 179 155
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t231 : ((208529016087/5000000000000 : ℚ) : ℝ) ≤ stT179 231 := by
  have hc : ((316937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208529016087/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((316937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c232 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-21621/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414347/1000000) (δ := 8989/1000000000) (ψ := -4681/8000) 179 155
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t232 : ((-28406213311/5000000000000 : ℚ) : ℝ) ≤ stT179 232 := by
  have hc : ((-43267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28406213311/5000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-43267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c233 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-755547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1517053/2500000) (δ := 9089/1000000000) (ψ := -4681/8000) 179 155
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t233 : ((-247504108917/5000000000000 : ℚ) : ℝ) ≤ stT179 233 := by
  have hc : ((-755597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247504108917/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-755597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c234 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-998633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7723243/10000000) (δ := 9081/1000000000) (ψ := -4681/8000) 179 156
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t234 : ((-652860049443/10000000000000 : ℚ) : ℝ) ≤ stT179 234 := by
  have hc : ((-998683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-652860049443/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-998683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c235 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-137083/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1453731/2500000) (δ := 9081/1000000000) (ψ := -4681/8000) 179 156
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t235 : ((-89429739597/2000000000000 : ℚ) : ℝ) ≤ stT179 235 := by
  have hc : ((-137093/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89429739597/2000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-137093/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c236 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((983/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -244669/625000) (δ := 4561/500000000) (ψ := -4681/8000) 179 156
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t236 : ((9896383/31250000000 : ℚ) : ℝ) ≤ stT179 236 := by
  have hc : ((973/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9896383/31250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((973/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c237 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((690211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101127/500000) (δ := 4511/500000000) (ψ := -4681/8000) 179 156
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t237 : ((448307190609/10000000000000 : ℚ) : ℝ) ≤ stT179 237 := by
  have hc : ((690161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448307190609/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((690161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c238 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((998469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138341/10000000) (δ := 4561/500000000) (ψ := -4681/8000) 179 156
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t238 : ((647178191057/10000000000000 : ℚ) : ℝ) ≤ stT179 238 := by
  have hc : ((998419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((647178191057/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((998419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c239 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((76793/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1737981/10000000) (δ := 9081/1000000000) (ψ := -4681/8000) 179 156
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t239 : ((6208751331/125000000000 : ℚ) : ℝ) ≤ stT179 239 := by
  have hc : ((19197/25000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6208751331/125000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((19197/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c240 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((7991/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3606473/10000000) (δ := 4511/500000000) (ψ := -4681/8000) 179 156
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t240 : ((41249194791/5000000000000 : ℚ) : ℝ) ≤ stT179 240 := by
  have hc : ((63903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41249194791/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((63903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c241 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-144459/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2733589/5000000) (δ := 4511/500000000) (ψ := -4681/8000) 179 156
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t241 : ((-186124656051/5000000000000 : ℚ) : ℝ) ≤ stT179 241 := by
  have hc : ((-288943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186124656051/5000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-288943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c242 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-977291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3660093/5000000) (δ := 4511/500000000) (ψ := -4681/8000) 179 156
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t242 : ((-25130369133/400000000000 : ℚ) : ℝ) ≤ stT179 242 := by
  have hc : ((-977341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25130369133/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-977341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c243 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-108189/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3271211/5000000) (δ := 4537/500000000) (ψ := -4681/8000) 179 157
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t243 : ((-277629444281/5000000000000 : ℚ) : ℝ) ≤ stT179 243 := by
  have hc : ((-432781/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277629444281/5000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-432781/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c244 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-306063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4704629/10000000) (δ := 4537/500000000) (ψ := -4681/8000) 179 157
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t244 : ((-39193790181/2000000000000 : ℚ) : ℝ) ≤ stT179 244 := by
  have hc : ((-306113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39193790181/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-306113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c245 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((81743/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -359297/1250000) (δ := 17929/1000000000) (ψ := -4681/8000) 179 157
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t245 : ((13054313027/500000000000 : ℚ) : ℝ) ≤ stT179 245 := by
  have hc : ((81733/200000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13054313027/500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((81733/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c246 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((228209/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32861/312500) (δ := 4487/500000000) (ψ := -4681/8000) 179 157
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t246 : ((36373152921/625000000000 : ℚ) : ℝ) ≤ stT179 246 := by
  have hc : ((456393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36373152921/625000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((456393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c247 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((953683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381933/5000000) (δ := 4487/500000000) (ψ := -4681/8000) 179 157
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t247 : ((151695354943/2500000000000 : ℚ) : ℝ) ≤ stT179 247 := by
  have hc : ((953633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151695354943/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((953633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c248 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((257933/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 514389/2000000) (δ := 4487/500000000) (ψ := -4681/8000) 179 157
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t248 : ((8188579/250000000 : ℚ) : ℝ) ≤ stT179 248 := by
  have hc : ((64477/125000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8188579/250000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((64477/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c249 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-177353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 437273/1000000) (δ := 9029/1000000000) (ψ := -4681/8000) 179 157
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t249 : ((-4496988647/400000000000 : ℚ) : ℝ) ≤ stT179 249 := by
  have hc : ((-177403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4496988647/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-177403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_c250 :
    |Real.cos (((179 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((-31227/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1233271/2000000) (δ := 9129/1000000000) (ψ := -4681/8000) 179 157
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st179_t250 : ((-2468871053/50000000000 : ℚ) : ℝ) ≤ stT179 250 := by
  have hc : ((-31229/40000 : ℚ) : ℝ)
      ≤ Real.cos (((179 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st179_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2468871053/50000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-31229/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st179_p1 : ((833593/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT179 (i+1) := by
  rw [Finset.sum_range_one]
  exact st179_t1

theorem st179_p2 : ((2424971037189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT179 (i+1))
      = (∑ i ∈ Finset.range 1, stT179 (i+1)) + stT179 2 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 1
    simpa using h
  have hprev := st179_p1
  have hstep := st179_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p3 : ((7648415822919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT179 (i+1))
      = (∑ i ∈ Finset.range 2, stT179 (i+1)) + stT179 3 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 2
    simpa using h
  have hprev := st179_p2
  have hstep := st179_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p4 : ((3375104968257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT179 (i+1))
      = (∑ i ∈ Finset.range 3, stT179 (i+1)) + stT179 4 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 3
    simpa using h
  have hprev := st179_p3
  have hstep := st179_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p5 : ((118324975933/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT179 (i+1))
      = (∑ i ∈ Finset.range 4, stT179 (i+1)) + stT179 5 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 4
    simpa using h
  have hprev := st179_p4
  have hstep := st179_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p6 : ((5106259536733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT179 (i+1))
      = (∑ i ∈ Finset.range 5, stT179 (i+1)) + stT179 6 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 5
    simpa using h
  have hprev := st179_p5
  have hstep := st179_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p7 : ((203064307223/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT179 (i+1))
      = (∑ i ∈ Finset.range 6, stT179 (i+1)) + stT179 7 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 6
    simpa using h
  have hprev := st179_p6
  have hstep := st179_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p8 : ((1180361231267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT179 (i+1))
      = (∑ i ∈ Finset.range 7, stT179 (i+1)) + stT179 8 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 7
    simpa using h
  have hprev := st179_p7
  have hstep := st179_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p9 : ((348005467679/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT179 (i+1))
      = (∑ i ∈ Finset.range 8, stT179 (i+1)) + stT179 9 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 8
    simpa using h
  have hprev := st179_p8
  have hstep := st179_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p10 : ((582923889259/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT179 (i+1))
      = (∑ i ∈ Finset.range 9, stT179 (i+1)) + stT179 10 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 9
    simpa using h
  have hprev := st179_p9
  have hstep := st179_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p11 : ((-43535391863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT179 (i+1))
      = (∑ i ∈ Finset.range 10, stT179 (i+1)) + stT179 11 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 10
    simpa using h
  have hprev := st179_p10
  have hstep := st179_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p12 : ((1990762911243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT179 (i+1))
      = (∑ i ∈ Finset.range 11, stT179 (i+1)) + stT179 12 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 11
    simpa using h
  have hprev := st179_p11
  have hstep := st179_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p13 : ((3398136657243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT179 (i+1))
      = (∑ i ∈ Finset.range 12, stT179 (i+1)) + stT179 13 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 12
    simpa using h
  have hprev := st179_p12
  have hstep := st179_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p14 : ((590909408391/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT179 (i+1))
      = (∑ i ∈ Finset.range 13, stT179 (i+1)) + stT179 14 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 13
    simpa using h
  have hprev := st179_p13
  have hstep := st179_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p15 : ((3083321111467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT179 (i+1))
      = (∑ i ∈ Finset.range 14, stT179 (i+1)) + stT179 15 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 14
    simpa using h
  have hprev := st179_p14
  have hstep := st179_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p16 : ((5268863611467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT179 (i+1))
      = (∑ i ∈ Finset.range 15, stT179 (i+1)) + stT179 16 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 15
    simpa using h
  have hprev := st179_p15
  have hstep := st179_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p17 : ((6130168160967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT179 (i+1))
      = (∑ i ∈ Finset.range 16, stT179 (i+1)) + stT179 17 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 16
    simpa using h
  have hprev := st179_p16
  have hstep := st179_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p18 : ((792023673493/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT179 (i+1))
      = (∑ i ∈ Finset.range 17, stT179 (i+1)) + stT179 18 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 17
    simpa using h
  have hprev := st179_p17
  have hstep := st179_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p19 : ((3114562262137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT179 (i+1))
      = (∑ i ∈ Finset.range 18, stT179 (i+1)) + stT179 19 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 18
    simpa using h
  have hprev := st179_p18
  have hstep := st179_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p20 : ((416182822871/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT179 (i+1))
      = (∑ i ∈ Finset.range 19, stT179 (i+1)) + stT179 20 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 19
    simpa using h
  have hprev := st179_p19
  have hstep := st179_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p21 : ((1296367072227/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT179 (i+1))
      = (∑ i ∈ Finset.range 20, stT179 (i+1)) + stT179 21 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 20
    simpa using h
  have hprev := st179_p20
  have hstep := st179_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p22 : ((6405635083071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT179 (i+1))
      = (∑ i ∈ Finset.range 21, stT179 (i+1)) + stT179 22 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 21
    simpa using h
  have hprev := st179_p21
  have hstep := st179_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p23 : ((286385595321/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT179 (i+1))
      = (∑ i ∈ Finset.range 22, stT179 (i+1)) + stT179 23 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 22
    simpa using h
  have hprev := st179_p22
  have hstep := st179_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p24 : ((400277056053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT179 (i+1))
      = (∑ i ∈ Finset.range 23, stT179 (i+1)) + stT179 24 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 23
    simpa using h
  have hprev := st179_p23
  have hstep := st179_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p25 : ((469749806053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT179 (i+1))
      = (∑ i ∈ Finset.range 24, stT179 (i+1)) + stT179 25 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 24
    simpa using h
  have hprev := st179_p24
  have hstep := st179_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p26 : ((5427964301983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT179 (i+1))
      = (∑ i ∈ Finset.range 25, stT179 (i+1)) + stT179 26 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 25
    simpa using h
  have hprev := st179_p25
  have hstep := st179_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p27 : ((7346290505983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT179 (i+1))
      = (∑ i ∈ Finset.range 26, stT179 (i+1)) + stT179 27 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 26
    simpa using h
  have hprev := st179_p26
  have hstep := st179_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p28 : ((9215598488173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT179 (i+1))
      = (∑ i ∈ Finset.range 27, stT179 (i+1)) + stT179 28 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 27
    simpa using h
  have hprev := st179_p27
  have hstep := st179_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p29 : ((2210578756743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT179 (i+1))
      = (∑ i ∈ Finset.range 28, stT179 (i+1)) + stT179 29 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 28
    simpa using h
  have hprev := st179_p28
  have hstep := st179_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p30 : ((12874132506409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT179 (i+1))
      = (∑ i ∈ Finset.range 29, stT179 (i+1)) + stT179 30 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 29
    simpa using h
  have hprev := st179_p29
  have hstep := st179_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p31 : ((14464372201033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT179 (i+1))
      = (∑ i ∈ Finset.range 30, stT179 (i+1)) + stT179 31 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 30
    simpa using h
  have hprev := st179_p30
  have hstep := st179_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p32 : ((3058408755553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT179 (i+1))
      = (∑ i ∈ Finset.range 31, stT179 (i+1)) + stT179 32 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 31
    simpa using h
  have hprev := st179_p31
  have hstep := st179_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p33 : ((924869937749/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT179 (i+1))
      = (∑ i ∈ Finset.range 32, stT179 (i+1)) + stT179 33 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 32
    simpa using h
  have hprev := st179_p32
  have hstep := st179_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p34 : ((3295764329159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT179 (i+1))
      = (∑ i ∈ Finset.range 33, stT179 (i+1)) + stT179 34 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 33
    simpa using h
  have hprev := st179_p33
  have hstep := st179_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p35 : ((11947209865303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT179 (i+1))
      = (∑ i ∈ Finset.range 34, stT179 (i+1)) + stT179 35 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 34
    simpa using h
  have hprev := st179_p34
  have hstep := st179_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p36 : ((2525552585283/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT179 (i+1))
      = (∑ i ∈ Finset.range 35, stT179 (i+1)) + stT179 36 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 35
    simpa using h
  have hprev := st179_p35
  have hstep := st179_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p37 : ((14228883269251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT179 (i+1))
      = (∑ i ∈ Finset.range 36, stT179 (i+1)) + stT179 37 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 36
    simpa using h
  have hprev := st179_p36
  have hstep := st179_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p38 : ((6979230825483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT179 (i+1))
      = (∑ i ∈ Finset.range 37, stT179 (i+1)) + stT179 38 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 37
    simpa using h
  have hprev := st179_p37
  have hstep := st179_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p39 : ((6199670703013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT179 (i+1))
      = (∑ i ∈ Finset.range 38, stT179 (i+1)) + stT179 39 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 38
    simpa using h
  have hprev := st179_p38
  have hstep := st179_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p40 : ((1303054434473/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT179 (i+1))
      = (∑ i ∈ Finset.range 39, stT179 (i+1)) + stT179 40 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 39
    simpa using h
  have hprev := st179_p39
  have hstep := st179_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p41 : ((3555450742529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT179 (i+1))
      = (∑ i ∈ Finset.range 40, stT179 (i+1)) + stT179 41 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 40
    simpa using h
  have hprev := st179_p40
  have hstep := st179_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p42 : ((6422568676481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT179 (i+1))
      = (∑ i ∈ Finset.range 41, stT179 (i+1)) + stT179 42 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 41
    simpa using h
  have hprev := st179_p41
  have hstep := st179_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p43 : ((12893352803707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT179 (i+1))
      = (∑ i ∈ Finset.range 42, stT179 (i+1)) + stT179 43 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 42
    simpa using h
  have hprev := st179_p42
  have hstep := st179_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p44 : ((14112364092863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT179 (i+1))
      = (∑ i ∈ Finset.range 43, stT179 (i+1)) + stT179 44 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 43
    simpa using h
  have hprev := st179_p43
  have hstep := st179_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p45 : ((12668697472871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT179 (i+1))
      = (∑ i ∈ Finset.range 44, stT179 (i+1)) + stT179 45 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 44
    simpa using h
  have hprev := st179_p44
  have hstep := st179_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p46 : ((3352246021331/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT179 (i+1))
      = (∑ i ∈ Finset.range 45, stT179 (i+1)) + stT179 46 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 45
    simpa using h
  have hprev := st179_p45
  have hstep := st179_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p47 : ((1367287411051/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT179 (i+1))
      = (∑ i ∈ Finset.range 46, stT179 (i+1)) + stT179 47 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 46
    simpa using h
  have hprev := st179_p46
  have hstep := st179_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p48 : ((6314222896767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT179 (i+1))
      = (∑ i ∈ Finset.range 47, stT179 (i+1)) + stT179 48 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 47
    simpa using h
  have hprev := st179_p47
  have hstep := st179_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p49 : ((7012388401603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT179 (i+1))
      = (∑ i ∈ Finset.range 48, stT179 (i+1)) + stT179 49 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 48
    simpa using h
  have hprev := st179_p48
  have hstep := st179_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p50 : ((1582348260799/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT179 (i+1))
      = (∑ i ∈ Finset.range 49, stT179 (i+1)) + stT179 50 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 49
    simpa using h
  have hprev := st179_p49
  have hstep := st179_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p51 : ((430015005661/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT179 (i+1))
      = (∑ i ∈ Finset.range 50, stT179 (i+1)) + stT179 51 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 50
    simpa using h
  have hprev := st179_p50
  have hstep := st179_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p52 : ((13010457289553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT179 (i+1))
      = (∑ i ∈ Finset.range 51, stT179 (i+1)) + stT179 52 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 51
    simpa using h
  have hprev := st179_p51
  have hstep := st179_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p53 : ((3355178317127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT179 (i+1))
      = (∑ i ∈ Finset.range 52, stT179 (i+1)) + stT179 53 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 52
    simpa using h
  have hprev := st179_p52
  have hstep := st179_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p54 : ((1660757927549/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT179 (i+1))
      = (∑ i ∈ Finset.range 53, stT179 (i+1)) + stT179 54 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 53
    simpa using h
  have hprev := st179_p53
  have hstep := st179_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p55 : ((1653362964849/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT179 (i+1))
      = (∑ i ∈ Finset.range 54, stT179 (i+1)) + stT179 55 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 54
    simpa using h
  have hprev := st179_p54
  have hstep := st179_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p56 : ((6698414863029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT179 (i+1))
      = (∑ i ∈ Finset.range 55, stT179 (i+1)) + stT179 56 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 55
    simpa using h
  have hprev := st179_p55
  have hstep := st179_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p57 : ((6596669536101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT179 (i+1))
      = (∑ i ∈ Finset.range 56, stT179 (i+1)) + stT179 57 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 56
    simpa using h
  have hprev := st179_p56
  have hstep := st179_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p58 : ((6678966478833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT179 (i+1))
      = (∑ i ∈ Finset.range 57, stT179 (i+1)) + stT179 58 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 57
    simpa using h
  have hprev := st179_p57
  have hstep := st179_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p59 : ((6650278030793/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT179 (i+1))
      = (∑ i ∈ Finset.range 58, stT179 (i+1)) + stT179 59 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 58
    simpa using h
  have hprev := st179_p58
  have hstep := st179_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p60 : ((13185635559671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT179 (i+1))
      = (∑ i ∈ Finset.range 59, stT179 (i+1)) + stT179 60 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 59
    simpa using h
  have hprev := st179_p59
  have hstep := st179_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p61 : ((13529470703863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT179 (i+1))
      = (∑ i ∈ Finset.range 60, stT179 (i+1)) + stT179 61 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 60
    simpa using h
  have hprev := st179_p60
  have hstep := st179_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p62 : ((12917310689833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT179 (i+1))
      = (∑ i ∈ Finset.range 61, stT179 (i+1)) + stT179 62 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 61
    simpa using h
  have hprev := st179_p61
  have hstep := st179_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p63 : ((13803669730239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT179 (i+1))
      = (∑ i ∈ Finset.range 62, stT179 (i+1)) + stT179 63 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 62
    simpa using h
  have hprev := st179_p62
  have hstep := st179_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p64 : ((3171966271899/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT179 (i+1))
      = (∑ i ∈ Finset.range 63, stT179 (i+1)) + stT179 64 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 63
    simpa using h
  have hprev := st179_p63
  have hstep := st179_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p65 : ((6960889824027/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT179 (i+1))
      = (∑ i ∈ Finset.range 64, stT179 (i+1)) + stT179 65 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 64
    simpa using h
  have hprev := st179_p64
  have hstep := st179_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p66 : ((3187118482971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT179 (i+1))
      = (∑ i ∈ Finset.range 65, stT179 (i+1)) + stT179 66 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 65
    simpa using h
  have hprev := st179_p65
  have hstep := st179_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p67 : ((1704544338339/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT179 (i+1))
      = (∑ i ∈ Finset.range 66, stT179 (i+1)) + stT179 67 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 66
    simpa using h
  have hprev := st179_p66
  have hstep := st179_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p68 : ((13250248627223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT179 (i+1))
      = (∑ i ∈ Finset.range 67, stT179 (i+1)) + stT179 68 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 67
    simpa using h
  have hprev := st179_p67
  have hstep := st179_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p69 : ((13005795426401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT179 (i+1))
      = (∑ i ∈ Finset.range 68, stT179 (i+1)) + stT179 69 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 68
    simpa using h
  have hprev := st179_p68
  have hstep := st179_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p70 : ((13838156986513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT179 (i+1))
      = (∑ i ∈ Finset.range 69, stT179 (i+1)) + stT179 70 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 69
    simpa using h
  have hprev := st179_p69
  have hstep := st179_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p71 : ((12674456709631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT179 (i+1))
      = (∑ i ∈ Finset.range 70, stT179 (i+1)) + stT179 71 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 70
    simpa using h
  have hprev := st179_p70
  have hstep := st179_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p72 : ((343513414543/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT179 (i+1))
      = (∑ i ∈ Finset.range 71, stT179 (i+1)) + stT179 72 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 71
    simpa using h
  have hprev := st179_p71
  have hstep := st179_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p73 : ((1652876645857/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT179 (i+1))
      = (∑ i ∈ Finset.range 72, stT179 (i+1)) + stT179 73 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 72
    simpa using h
  have hprev := st179_p72
  have hstep := st179_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p74 : ((202146104981/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT179 (i+1))
      = (∑ i ∈ Finset.range 73, stT179 (i+1)) + stT179 74 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 73
    simpa using h
  have hprev := st179_p73
  have hstep := st179_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p75 : ((3475200305471/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT179 (i+1))
      = (∑ i ∈ Finset.range 74, stT179 (i+1)) + stT179 75 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 74
    simpa using h
  have hprev := st179_p74
  have hstep := st179_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p76 : ((6386830374531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT179 (i+1))
      = (∑ i ∈ Finset.range 75, stT179 (i+1)) + stT179 76 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 75
    simpa using h
  have hprev := st179_p75
  have hstep := st179_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p77 : ((13400152899787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT179 (i+1))
      = (∑ i ∈ Finset.range 76, stT179 (i+1)) + stT179 77 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 76
    simpa using h
  have hprev := st179_p76
  have hstep := st179_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p78 : ((13679967985689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT179 (i+1))
      = (∑ i ∈ Finset.range 77, stT179 (i+1)) + stT179 78 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 77
    simpa using h
  have hprev := st179_p77
  have hstep := st179_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p79 : ((12671633742713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT179 (i+1))
      = (∑ i ∈ Finset.range 78, stT179 (i+1)) + stT179 79 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 78
    simpa using h
  have hprev := st179_p78
  have hstep := st179_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p80 : ((2737541321049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT179 (i+1))
      = (∑ i ∈ Finset.range 79, stT179 (i+1)) + stT179 80 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 79
    simpa using h
  have hprev := st179_p79
  have hstep := st179_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p81 : ((2688479059577/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT179 (i+1))
      = (∑ i ∈ Finset.range 80, stT179 (i+1)) + stT179 81 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 80
    simpa using h
  have hprev := st179_p80
  have hstep := st179_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p82 : ((12711947688317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT179 (i+1))
      = (∑ i ∈ Finset.range 81, stT179 (i+1)) + stT179 82 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 81
    simpa using h
  have hprev := st179_p81
  have hstep := st179_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p83 : ((13801141137843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT179 (i+1))
      = (∑ i ∈ Finset.range 82, stT179 (i+1)) + stT179 83 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 82
    simpa using h
  have hprev := st179_p82
  have hstep := st179_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p84 : ((13327298208283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT179 (i+1))
      = (∑ i ∈ Finset.range 83, stT179 (i+1)) + stT179 84 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 83
    simpa using h
  have hprev := st179_p83
  have hstep := st179_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p85 : ((12738247026349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT179 (i+1))
      = (∑ i ∈ Finset.range 84, stT179 (i+1)) + stT179 85 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 84
    simpa using h
  have hprev := st179_p84
  have hstep := st179_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p86 : ((1726888033331/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT179 (i+1))
      = (∑ i ∈ Finset.range 85, stT179 (i+1)) + stT179 86 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 85
    simpa using h
  have hprev := st179_p85
  have hstep := st179_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p87 : ((2670254989469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT179 (i+1))
      = (∑ i ∈ Finset.range 86, stT179 (i+1)) + stT179 87 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 86
    simpa using h
  have hprev := st179_p86
  have hstep := st179_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p88 : ((12707362693173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT179 (i+1))
      = (∑ i ∈ Finset.range 87, stT179 (i+1)) + stT179 88 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 87
    simpa using h
  have hprev := st179_p87
  have hstep := st179_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p89 : ((6873434445583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT179 (i+1))
      = (∑ i ∈ Finset.range 88, stT179 (i+1)) + stT179 89 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 88
    simpa using h
  have hprev := st179_p88
  have hstep := st179_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p90 : ((2700780723389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT179 (i+1))
      = (∑ i ∈ Finset.range 89, stT179 (i+1)) + stT179 90 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 89
    simpa using h
  have hprev := st179_p89
  have hstep := st179_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p91 : ((253256305841/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT179 (i+1))
      = (∑ i ∈ Finset.range 90, stT179 (i+1)) + stT179 91 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 90
    simpa using h
  have hprev := st179_p90
  have hstep := st179_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p92 : ((6776977375811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT179 (i+1))
      = (∑ i ∈ Finset.range 91, stT179 (i+1)) + stT179 92 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 91
    simpa using h
  have hprev := st179_p91
  have hstep := st179_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p93 : ((2748169508241/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT179 (i+1))
      = (∑ i ∈ Finset.range 92, stT179 (i+1)) + stT179 93 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 92
    simpa using h
  have hprev := st179_p92
  have hstep := st179_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p94 : ((12722943357937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT179 (i+1))
      = (∑ i ∈ Finset.range 93, stT179 (i+1)) + stT179 94 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 93
    simpa using h
  have hprev := st179_p93
  have hstep := st179_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p95 : ((13201926317127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT179 (i+1))
      = (∑ i ∈ Finset.range 94, stT179 (i+1)) + stT179 95 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 94
    simpa using h
  have hprev := st179_p94
  have hstep := st179_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p96 : ((13920702034607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT179 (i+1))
      = (∑ i ∈ Finset.range 95, stT179 (i+1)) + stT179 96 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 95
    simpa using h
  have hprev := st179_p95
  have hstep := st179_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p97 : ((1628536021579/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT179 (i+1))
      = (∑ i ∈ Finset.range 96, stT179 (i+1)) + stT179 97 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 96
    simpa using h
  have hprev := st179_p96
  have hstep := st179_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p98 : ((6397900729841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT179 (i+1))
      = (∑ i ∈ Finset.range 97, stT179 (i+1)) + stT179 98 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 97
    simpa using h
  have hprev := st179_p97
  have hstep := st179_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p99 : ((6900342847029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT179 (i+1))
      = (∑ i ∈ Finset.range 98, stT179 (i+1)) + stT179 99 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 98
    simpa using h
  have hprev := st179_p98
  have hstep := st179_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p100 : ((6780247847029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT179 (i+1))
      = (∑ i ∈ Finset.range 99, stT179 (i+1)) + stT179 100 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 99
    simpa using h
  have hprev := st179_p99
  have hstep := st179_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p101 : ((6332848911089/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT179 (i+1))
      = (∑ i ∈ Finset.range 100, stT179 (i+1)) + stT179 101 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 100
    simpa using h
  have hprev := st179_p100
  have hstep := st179_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p102 : ((13261398971641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT179 (i+1))
      = (∑ i ∈ Finset.range 101, stT179 (i+1)) + stT179 102 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 101
    simpa using h
  have hprev := st179_p101
  have hstep := st179_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p103 : ((6966368067599/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT179 (i+1))
      = (∑ i ∈ Finset.range 102, stT179 (i+1)) + stT179 103 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 102
    simpa using h
  have hprev := st179_p102
  have hstep := st179_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p104 : ((2623681940401/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT179 (i+1))
      = (∑ i ∈ Finset.range 103, stT179 (i+1)) + stT179 104 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 103
    simpa using h
  have hprev := st179_p103
  have hstep := st179_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p105 : ((253898251671/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT179 (i+1))
      = (∑ i ∈ Finset.range 104, stT179 (i+1)) + stT179 105 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 104
    simpa using h
  have hprev := st179_p104
  have hstep := st179_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p106 : ((2723188465273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT179 (i+1))
      = (∑ i ∈ Finset.range 105, stT179 (i+1)) + stT179 106 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 105
    simpa using h
  have hprev := st179_p105
  have hstep := st179_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p107 : ((13820210742957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT179 (i+1))
      = (∑ i ∈ Finset.range 106, stT179 (i+1)) + stT179 107 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 106
    simpa using h
  have hprev := st179_p106
  have hstep := st179_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p108 : ((1608084171023/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT179 (i+1))
      = (∑ i ∈ Finset.range 107, stT179 (i+1)) + stT179 108 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 107
    simpa using h
  have hprev := st179_p107
  have hstep := st179_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p109 : ((3206665740379/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT179 (i+1))
      = (∑ i ∈ Finset.range 108, stT179 (i+1)) + stT179 109 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 108
    simpa using h
  have hprev := st179_p108
  have hstep := st179_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p110 : ((6889898008563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT179 (i+1))
      = (∑ i ∈ Finset.range 109, stT179 (i+1)) + stT179 110 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 109
    simpa using h
  have hprev := st179_p109
  have hstep := st179_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p111 : ((6855065808279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT179 (i+1))
      = (∑ i ∈ Finset.range 110, stT179 (i+1)) + stT179 111 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 110
    simpa using h
  have hprev := st179_p110
  have hstep := st179_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p112 : ((1277067742827/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT179 (i+1))
      = (∑ i ∈ Finset.range 111, stT179 (i+1)) + stT179 112 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 111
    simpa using h
  have hprev := st179_p111
  have hstep := st179_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p113 : ((1289102185643/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT179 (i+1))
      = (∑ i ∈ Finset.range 112, stT179 (i+1)) + stT179 113 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 112
    simpa using h
  have hprev := st179_p112
  have hstep := st179_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p114 : ((2763816973903/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT179 (i+1))
      = (∑ i ∈ Finset.range 113, stT179 (i+1)) + stT179 114 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 113
    simpa using h
  have hprev := st179_p113
  have hstep := st179_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p115 : ((2740154846029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT179 (i+1))
      = (∑ i ∈ Finset.range 114, stT179 (i+1)) + stT179 115 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 114
    simpa using h
  have hprev := st179_p114
  have hstep := st179_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p116 : ((99824040651/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT179 (i+1))
      = (∑ i ∈ Finset.range 115, stT179 (i+1)) + stT179 116 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 115
    simpa using h
  have hprev := st179_p115
  have hstep := st179_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p117 : ((3210951363957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT179 (i+1))
      = (∑ i ∈ Finset.range 116, stT179 (i+1)) + stT179 117 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 116
    simpa using h
  have hprev := st179_p116
  have hstep := st179_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p118 : ((860253578433/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT179 (i+1))
      = (∑ i ∈ Finset.range 117, stT179 (i+1)) + stT179 118 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 117
    simpa using h
  have hprev := st179_p117
  have hstep := st179_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p119 : ((3449199968523/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT179 (i+1))
      = (∑ i ∈ Finset.range 118, stT179 (i+1)) + stT179 119 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 118
    simpa using h
  have hprev := st179_p118
  have hstep := st179_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p120 : ((6444632758979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT179 (i+1))
      = (∑ i ∈ Finset.range 119, stT179 (i+1)) + stT179 120 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 119
    simpa using h
  have hprev := st179_p119
  have hstep := st179_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p121 : ((2542799827359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT179 (i+1))
      = (∑ i ∈ Finset.range 120, stT179 (i+1)) + stT179 121 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 120
    simpa using h
  have hprev := st179_p120
  have hstep := st179_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p122 : ((13581119289257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT179 (i+1))
      = (∑ i ∈ Finset.range 121, stT179 (i+1)) + stT179 122 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 121
    simpa using h
  have hprev := st179_p121
  have hstep := st179_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p123 : ((13933080373393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT179 (i+1))
      = (∑ i ∈ Finset.range 122, stT179 (i+1)) + stT179 123 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 122
    simpa using h
  have hprev := st179_p122
  have hstep := st179_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p124 : ((13154808865951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT179 (i+1))
      = (∑ i ∈ Finset.range 123, stT179 (i+1)) + stT179 124 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 123
    simpa using h
  have hprev := st179_p123
  have hstep := st179_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p125 : ((12609567346007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT179 (i+1))
      = (∑ i ∈ Finset.range 124, stT179 (i+1)) + stT179 125 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 124
    simpa using h
  have hprev := st179_p124
  have hstep := st179_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p126 : ((13230211530647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT179 (i+1))
      = (∑ i ∈ Finset.range 125, stT179 (i+1)) + stT179 126 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 125
    simpa using h
  have hprev := st179_p125
  have hstep := st179_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p127 : ((13954918725271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT179 (i+1))
      = (∑ i ∈ Finset.range 126, stT179 (i+1)) + stT179 127 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 126
    simpa using h
  have hprev := st179_p126
  have hstep := st179_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p128 : ((13571871683959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT179 (i+1))
      = (∑ i ∈ Finset.range 127, stT179 (i+1)) + stT179 128 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 127
    simpa using h
  have hprev := st179_p127
  have hstep := st179_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p129 : ((1590420760949/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT179 (i+1))
      = (∑ i ∈ Finset.range 128, stT179 (i+1)) + stT179 129 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 128
    simpa using h
  have hprev := st179_p128
  have hstep := st179_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p130 : ((6397506039277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT179 (i+1))
      = (∑ i ∈ Finset.range 129, stT179 (i+1)) + stT179 130 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 129
    simpa using h
  have hprev := st179_p129
  have hstep := st179_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p131 : ((6831333712881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT179 (i+1))
      = (∑ i ∈ Finset.range 130, stT179 (i+1)) + stT179 131 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 130
    simpa using h
  have hprev := st179_p130
  have hstep := st179_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p132 : ((6971048394641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT179 (i+1))
      = (∑ i ∈ Finset.range 131, stT179 (i+1)) + stT179 132 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 131
    simpa using h
  have hprev := st179_p131
  have hstep := st179_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p133 : ((6600671029241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT179 (i+1))
      = (∑ i ∈ Finset.range 132, stT179 (i+1)) + stT179 133 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 132
    simpa using h
  have hprev := st179_p132
  have hstep := st179_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p134 : ((62978944473/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT179 (i+1))
      = (∑ i ∈ Finset.range 133, stT179 (i+1)) + stT179 134 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 133
    simpa using h
  have hprev := st179_p133
  have hstep := st179_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p135 : ((3262162576109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT179 (i+1))
      = (∑ i ∈ Finset.range 134, stT179 (i+1)) + stT179 135 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 134
    simpa using h
  have hprev := st179_p134
  have hstep := st179_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p136 : ((346666948753/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT179 (i+1))
      = (∑ i ∈ Finset.range 135, stT179 (i+1)) + stT179 136 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 135
    simpa using h
  have hprev := st179_p135
  have hstep := st179_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p137 : ((6914111221091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT179 (i+1))
      = (∑ i ∈ Finset.range 136, stT179 (i+1)) + stT179 137 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 136
    simpa using h
  have hprev := st179_p136
  have hstep := st179_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p138 : ((12998191535477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT179 (i+1))
      = (∑ i ∈ Finset.range 137, stT179 (i+1)) + stT179 138 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 137
    simpa using h
  have hprev := st179_p137
  have hstep := st179_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p139 : ((12589742729771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT179 (i+1))
      = (∑ i ∈ Finset.range 138, stT179 (i+1)) + stT179 139 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 138
    simpa using h
  have hprev := st179_p138
  have hstep := st179_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p140 : ((13184555353739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT179 (i+1))
      = (∑ i ∈ Finset.range 139, stT179 (i+1)) + stT179 140 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 139
    simpa using h
  have hprev := st179_p139
  have hstep := st179_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p141 : ((557197256549/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT179 (i+1))
      = (∑ i ∈ Finset.range 140, stT179 (i+1)) + stT179 141 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 140
    simpa using h
  have hprev := st179_p140
  have hstep := st179_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p142 : ((551244099441/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT179 (i+1))
      = (∑ i ∈ Finset.range 141, stT179 (i+1)) + stT179 142 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 141
    simpa using h
  have hprev := st179_p141
  have hstep := st179_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p143 : ((6476292767551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT179 (i+1))
      = (∑ i ∈ Finset.range 142, stT179 (i+1)) + stT179 143 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 142
    simpa using h
  have hprev := st179_p142
  have hstep := st179_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p144 : ((393210033517/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT179 (i+1))
      = (∑ i ∈ Finset.range 143, stT179 (i+1)) + stT179 144 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 143
    simpa using h
  have hprev := st179_p143
  have hstep := st179_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p145 : ((3291525014843/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT179 (i+1))
      = (∑ i ∈ Finset.range 144, stT179 (i+1)) + stT179 145 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 144
    simpa using h
  have hprev := st179_p144
  have hstep := st179_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p146 : ((13915397901877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT179 (i+1))
      = (∑ i ∈ Finset.range 145, stT179 (i+1)) + stT179 146 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 145
    simpa using h
  have hprev := st179_p145
  have hstep := st179_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p147 : ((13841685038113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT179 (i+1))
      = (∑ i ∈ Finset.range 146, stT179 (i+1)) + stT179 147 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 146
    simpa using h
  have hprev := st179_p146
  have hstep := st179_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p148 : ((13048946484153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT179 (i+1))
      = (∑ i ∈ Finset.range 147, stT179 (i+1)) + stT179 148 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 147
    simpa using h
  have hprev := st179_p147
  have hstep := st179_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p149 : ((12564156117369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT179 (i+1))
      = (∑ i ∈ Finset.range 148, stT179 (i+1)) + stT179 149 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 148
    simpa using h
  have hprev := st179_p148
  have hstep := st179_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p150 : ((13000681823337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT179 (i+1))
      = (∑ i ∈ Finset.range 149, stT179 (i+1)) + stT179 150 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 149
    simpa using h
  have hprev := st179_p149
  have hstep := st179_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p151 : ((13800882005101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT179 (i+1))
      = (∑ i ∈ Finset.range 150, stT179 (i+1)) + stT179 151 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 150
    simpa using h
  have hprev := st179_p150
  have hstep := st179_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p152 : ((13967188139953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT179 (i+1))
      = (∑ i ∈ Finset.range 151, stT179 (i+1)) + stT179 152 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 151
    simpa using h
  have hprev := st179_p151
  have hstep := st179_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p153 : ((6650768926257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT179 (i+1))
      = (∑ i ∈ Finset.range 152, stT179 (i+1)) + stT179 153 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 152
    simpa using h
  have hprev := st179_p152
  have hstep := st179_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p154 : ((6309928360301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT179 (i+1))
      = (∑ i ∈ Finset.range 153, stT179 (i+1)) + stT179 154 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 153
    simpa using h
  have hprev := st179_p153
  have hstep := st179_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p155 : ((12740117078939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT179 (i+1))
      = (∑ i ∈ Finset.range 154, stT179 (i+1)) + stT179 155 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 154
    simpa using h
  have hprev := st179_p154
  have hstep := st179_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p156 : ((13511853974939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT179 (i+1))
      = (∑ i ∈ Finset.range 155, stT179 (i+1)) + stT179 156 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 155
    simpa using h
  have hprev := st179_p155
  have hstep := st179_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p157 : ((14023722392759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT179 (i+1))
      = (∑ i ∈ Finset.range 156, stT179 (i+1)) + stT179 157 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 156
    simpa using h
  have hprev := st179_p156
  have hstep := st179_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p158 : ((2736941775109/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT179 (i+1))
      = (∑ i ∈ Finset.range 157, stT179 (i+1)) + stT179 158 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 157
    simpa using h
  have hprev := st179_p157
  have hstep := st179_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p159 : ((12891618015997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT179 (i+1))
      = (∑ i ∈ Finset.range 158, stT179 (i+1)) + stT179 159 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 158
    simpa using h
  have hprev := st179_p158
  have hstep := st179_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p160 : ((12547829955227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT179 (i+1))
      = (∑ i ∈ Finset.range 159, stT179 (i+1)) + stT179 160 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 159
    simpa using h
  have hprev := st179_p159
  have hstep := st179_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p161 : ((13034368087507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT179 (i+1))
      = (∑ i ∈ Finset.range 160, stT179 (i+1)) + stT179 161 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 160
    simpa using h
  have hprev := st179_p160
  have hstep := st179_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p162 : ((13803869773891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT179 (i+1))
      = (∑ i ∈ Finset.range 161, stT179 (i+1)) + stT179 162 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 161
    simpa using h
  have hprev := st179_p161
  have hstep := st179_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p163 : ((14009914932751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT179 (i+1))
      = (∑ i ∈ Finset.range 162, stT179 (i+1)) + stT179 163 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 162
    simpa using h
  have hprev := st179_p162
  have hstep := st179_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p164 : ((6717205287703/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT179 (i+1))
      = (∑ i ∈ Finset.range 163, stT179 (i+1)) + stT179 164 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 163
    simpa using h
  have hprev := st179_p163
  have hstep := st179_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p165 : ((12701982367727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT179 (i+1))
      = (∑ i ∈ Finset.range 164, stT179 (i+1)) + stT179 165 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 164
    simpa using h
  have hprev := st179_p164
  have hstep := st179_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p166 : ((12591081255941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT179 (i+1))
      = (∑ i ∈ Finset.range 165, stT179 (i+1)) + stT179 166 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 165
    simpa using h
  have hprev := st179_p165
  have hstep := st179_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p167 : ((13212170167493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT179 (i+1))
      = (∑ i ∈ Finset.range 166, stT179 (i+1)) + stT179 167 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 166
    simpa using h
  have hprev := st179_p166
  have hstep := st179_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p168 : ((13913536075193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT179 (i+1))
      = (∑ i ∈ Finset.range 167, stT179 (i+1)) + stT179 168 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 167
    simpa using h
  have hprev := st179_p167
  have hstep := st179_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p169 : ((13974088322333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT179 (i+1))
      = (∑ i ∈ Finset.range 168, stT179 (i+1)) + stT179 169 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 168
    simpa using h
  have hprev := st179_p168
  have hstep := st179_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p170 : ((13338288142703/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT179 (i+1))
      = (∑ i ∈ Finset.range 169, stT179 (i+1)) + stT179 170 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 169
    simpa using h
  have hprev := st179_p169
  have hstep := st179_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p171 : ((12651753115503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT179 (i+1))
      = (∑ i ∈ Finset.range 170, stT179 (i+1)) + stT179 171 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 170
    simpa using h
  have hprev := st179_p170
  have hstep := st179_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p172 : ((1574720790453/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT179 (i+1))
      = (∑ i ∈ Finset.range 171, stT179 (i+1)) + stT179 172 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 171
    simpa using h
  have hprev := st179_p171
  have hstep := st179_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p173 : ((6611764008147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT179 (i+1))
      = (∑ i ∈ Finset.range 172, stT179 (i+1)) + stT179 173 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 172
    simpa using h
  have hprev := st179_p172
  have hstep := st179_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p174 : ((1739159582339/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT179 (i+1))
      = (∑ i ∈ Finset.range 173, stT179 (i+1)) + stT179 174 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 173
    simpa using h
  have hprev := st179_p173
  have hstep := st179_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p175 : ((1750206336167/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT179 (i+1))
      = (∑ i ∈ Finset.range 174, stT179 (i+1)) + stT179 175 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 174
    simpa using h
  have hprev := st179_p174
  have hstep := st179_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p176 : ((6704943720019/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT179 (i+1))
      = (∑ i ∈ Finset.range 175, stT179 (i+1)) + stT179 176 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 175
    simpa using h
  have hprev := st179_p175
  have hstep := st179_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p177 : ((63513862591/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT179 (i+1))
      = (∑ i ∈ Finset.range 176, stT179 (i+1)) + stT179 177 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 176
    simpa using h
  have hprev := st179_p176
  have hstep := st179_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p178 : ((3135477552239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT179 (i+1))
      = (∑ i ∈ Finset.range 177, stT179 (i+1)) + stT179 178 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 177
    simpa using h
  have hprev := st179_p177
  have hstep := st179_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p179 : ((3267751124189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT179 (i+1))
      = (∑ i ∈ Finset.range 178, stT179 (i+1)) + stT179 179 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 178
    simpa using h
  have hprev := st179_p178
  have hstep := st179_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p180 : ((1724935209767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT179 (i+1))
      = (∑ i ∈ Finset.range 179, stT179 (i+1)) + stT179 180 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 179
    simpa using h
  have hprev := st179_p179
  have hstep := st179_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p181 : ((3516385941359/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT179 (i+1))
      = (∑ i ∈ Finset.range 180, stT179 (i+1)) + stT179 181 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 180
    simpa using h
  have hprev := st179_p180
  have hstep := st179_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p182 : ((6817379087093/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT179 (i+1))
      = (∑ i ∈ Finset.range 181, stT179 (i+1)) + stT179 182 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 181
    simpa using h
  have hprev := st179_p181
  have hstep := st179_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p183 : ((6447917409937/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT179 (i+1))
      = (∑ i ∈ Finset.range 182, stT179 (i+1)) + stT179 183 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 182
    simpa using h
  have hprev := st179_p182
  have hstep := st179_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p184 : ((6250482988207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT179 (i+1))
      = (∑ i ∈ Finset.range 183, stT179 (i+1)) + stT179 184 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 183
    simpa using h
  have hprev := st179_p183
  have hstep := st179_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p185 : ((6395311323639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT179 (i+1))
      = (∑ i ∈ Finset.range 184, stT179 (i+1)) + stT179 185 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 184
    simpa using h
  have hprev := st179_p184
  have hstep := st179_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p186 : ((3377270740507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT179 (i+1))
      = (∑ i ∈ Finset.range 185, stT179 (i+1)) + stT179 186 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 185
    simpa using h
  have hprev := st179_p185
  have hstep := st179_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p187 : ((3509905199507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT179 (i+1))
      = (∑ i ∈ Finset.range 186, stT179 (i+1)) + stT179 187 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 186
    simpa using h
  have hprev := st179_p186
  have hstep := st179_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p188 : ((3483942688157/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT179 (i+1))
      = (∑ i ∈ Finset.range 187, stT179 (i+1)) + stT179 188 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 187
    simpa using h
  have hprev := st179_p187
  have hstep := st179_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p189 : ((13289989065049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT179 (i+1))
      = (∑ i ∈ Finset.range 188, stT179 (i+1)) + stT179 189 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 188
    simpa using h
  have hprev := st179_p188
  have hstep := st179_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p190 : ((3160476306483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT179 (i+1))
      = (∑ i ∈ Finset.range 189, stT179 (i+1)) + stT179 190 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 189
    simpa using h
  have hprev := st179_p189
  have hstep := st179_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p191 : ((12523071780107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT179 (i+1))
      = (∑ i ∈ Finset.range 190, stT179 (i+1)) + stT179 191 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 190
    simpa using h
  have hprev := st179_p190
  have hstep := st179_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p192 : ((13025319744139/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT179 (i+1))
      = (∑ i ∈ Finset.range 191, stT179 (i+1)) + stT179 192 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 191
    simpa using h
  have hprev := st179_p191
  have hstep := st179_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p193 : ((13739130047409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT179 (i+1))
      = (∑ i ∈ Finset.range 192, stT179 (i+1)) + stT179 193 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 192
    simpa using h
  have hprev := st179_p192
  have hstep := st179_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p194 : ((112750996249/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT179 (i+1))
      = (∑ i ∈ Finset.range 193, stT179 (i+1)) + stT179 194 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 193
    simpa using h
  have hprev := st179_p193
  have hstep := st179_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p195 : ((2762538968167/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT179 (i+1))
      = (∑ i ∈ Finset.range 194, stT179 (i+1)) + stT179 195 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 194
    simpa using h
  have hprev := st179_p194
  have hstep := st179_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p196 : ((2624177484251/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT179 (i+1))
      = (∑ i ∈ Finset.range 195, stT179 (i+1)) + stT179 196 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 195
    simpa using h
  have hprev := st179_p195
  have hstep := st179_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p197 : ((12557659146567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT179 (i+1))
      = (∑ i ∈ Finset.range 196, stT179 (i+1)) + stT179 197 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 196
    simpa using h
  have hprev := st179_p196
  have hstep := st179_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p198 : ((12553886910207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT179 (i+1))
      = (∑ i ∈ Finset.range 197, stT179 (i+1)) + stT179 198 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 197
    simpa using h
  have hprev := st179_p197
  have hstep := st179_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p199 : ((3276898642047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT179 (i+1))
      = (∑ i ∈ Finset.range 198, stT179 (i+1)) + stT179 199 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 198
    simpa using h
  have hprev := st179_p198
  have hstep := st179_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p200 : ((3449291084847/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT179 (i+1))
      = (∑ i ∈ Finset.range 199, stT179 (i+1)) + stT179 200 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 199
    simpa using h
  have hprev := st179_p199
  have hstep := st179_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p201 : ((3526785929307/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT179 (i+1))
      = (∑ i ∈ Finset.range 200, stT179 (i+1)) + stT179 201 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 200
    simpa using h
  have hprev := st179_p200
  have hstep := st179_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p202 : ((6905858846293/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT179 (i+1))
      = (∑ i ∈ Finset.range 201, stT179 (i+1)) + stT179 202 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 201
    simpa using h
  have hprev := st179_p201
  have hstep := st179_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p203 : ((205191643409/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT179 (i+1))
      = (∑ i ∈ Finset.range 202, stT179 (i+1)) + stT179 203 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 202
    simpa using h
  have hprev := st179_p202
  have hstep := st179_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p204 : ((12564860409661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT179 (i+1))
      = (∑ i ∈ Finset.range 203, stT179 (i+1)) + stT179 204 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 203
    simpa using h
  have hprev := st179_p203
  have hstep := st179_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p205 : ((782271755677/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT179 (i+1))
      = (∑ i ∈ Finset.range 204, stT179 (i+1)) + stT179 205 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 204
    simpa using h
  have hprev := st179_p204
  have hstep := st179_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p206 : ((6508444022681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT179 (i+1))
      = (∑ i ∈ Finset.range 205, stT179 (i+1)) + stT179 206 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 205
    simpa using h
  have hprev := st179_p205
  have hstep := st179_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p207 : ((6854296084717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT179 (i+1))
      = (∑ i ∈ Finset.range 206, stT179 (i+1)) + stT179 207 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 206
    simpa using h
  have hprev := st179_p206
  have hstep := st179_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p208 : ((14106068694809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT179 (i+1))
      = (∑ i ∈ Finset.range 207, stT179 (i+1)) + stT179 208 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 207
    simpa using h
  have hprev := st179_p207
  have hstep := st179_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p209 : ((6968123218437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT179 (i+1))
      = (∑ i ∈ Finset.range 208, stT179 (i+1)) + stT179 209 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 208
    simpa using h
  have hprev := st179_p208
  have hstep := st179_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p210 : ((41626458537/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT179 (i+1))
      = (∑ i ∈ Finset.range 209, stT179 (i+1)) + stT179 210 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 209
    simpa using h
  have hprev := st179_p209
  have hstep := st179_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p211 : ((634080919421/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT179 (i+1))
      = (∑ i ∈ Finset.range 210, stT179 (i+1)) + stT179 211 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 210
    simpa using h
  have hprev := st179_p210
  have hstep := st179_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p212 : ((2490186312553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT179 (i+1))
      = (∑ i ∈ Finset.range 211, stT179 (i+1)) + stT179 212 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 211
    simpa using h
  have hprev := st179_p211
  have hstep := st179_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p213 : ((12779312022893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT179 (i+1))
      = (∑ i ∈ Finset.range 212, stT179 (i+1)) + stT179 213 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 212
    simpa using h
  have hprev := st179_p212
  have hstep := st179_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p214 : ((13444467571293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT179 (i+1))
      = (∑ i ∈ Finset.range 213, stT179 (i+1)) + stT179 214 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 213
    simpa using h
  have hprev := st179_p213
  have hstep := st179_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p215 : ((14006542474309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT179 (i+1))
      = (∑ i ∈ Finset.range 214, stT179 (i+1)) + stT179 215 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 214
    simpa using h
  have hprev := st179_p214
  have hstep := st179_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p216 : ((3525057305173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT179 (i+1))
      = (∑ i ∈ Finset.range 215, stT179 (i+1)) + stT179 216 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 215
    simpa using h
  have hprev := st179_p215
  have hstep := st179_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p217 : ((13668817113587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT179 (i+1))
      = (∑ i ∈ Finset.range 216, stT179 (i+1)) + stT179 217 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 216
    simpa using h
  have hprev := st179_p216
  have hstep := st179_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p218 : ((12992683854359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT179 (i+1))
      = (∑ i ∈ Finset.range 217, stT179 (i+1)) + stT179 218 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 217
    simpa using h
  have hprev := st179_p217
  have hstep := st179_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p219 : ((12502861650299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT179 (i+1))
      = (∑ i ∈ Finset.range 218, stT179 (i+1)) + stT179 219 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 218
    simpa using h
  have hprev := st179_p218
  have hstep := st179_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p220 : ((12506007462833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT179 (i+1))
      = (∑ i ∈ Finset.range 219, stT179 (i+1)) + stT179 220 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 219
    simpa using h
  have hprev := st179_p219
  have hstep := st179_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p221 : ((12996193639313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT179 (i+1))
      = (∑ i ∈ Finset.range 220, stT179 (i+1)) + stT179 221 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 220
    simpa using h
  have hprev := st179_p220
  have hstep := st179_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p222 : ((13666343576469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT179 (i+1))
      = (∑ i ∈ Finset.range 221, stT179 (i+1)) + stT179 222 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 221
    simpa using h
  have hprev := st179_p221
  have hstep := st179_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p223 : ((14104060984617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT179 (i+1))
      = (∑ i ∈ Finset.range 222, stT179 (i+1)) + stT179 223 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 222
    simpa using h
  have hprev := st179_p222
  have hstep := st179_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p224 : ((14045016883791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT179 (i+1))
      = (∑ i ∈ Finset.range 223, stT179 (i+1)) + stT179 224 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 223
    simpa using h
  have hprev := st179_p223
  have hstep := st179_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p225 : ((13528713958973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT179 (i+1))
      = (∑ i ∈ Finset.range 224, stT179 (i+1)) + stT179 225 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 224
    simpa using h
  have hprev := st179_p224
  have hstep := st179_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p226 : ((6433710156521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT179 (i+1))
      = (∑ i ∈ Finset.range 225, stT179 (i+1)) + stT179 226 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 225
    simpa using h
  have hprev := st179_p225
  have hstep := st179_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p227 : ((6227158915859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT179 (i+1))
      = (∑ i ∈ Finset.range 226, stT179 (i+1)) + stT179 227 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 226
    simpa using h
  have hprev := st179_p226
  have hstep := st179_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p228 : ((6265161725737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT179 (i+1))
      = (∑ i ∈ Finset.range 227, stT179 (i+1)) + stT179 228 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 227
    simpa using h
  have hprev := st179_p227
  have hstep := st179_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p229 : ((6523643990527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT179 (i+1))
      = (∑ i ∈ Finset.range 228, stT179 (i+1)) + stT179 229 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 228
    simpa using h
  have hprev := st179_p228
  have hstep := st179_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p230 : ((6851410579067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT179 (i+1))
      = (∑ i ∈ Finset.range 229, stT179 (i+1)) + stT179 230 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 229
    simpa using h
  have hprev := st179_p229
  have hstep := st179_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p231 : ((3529969797577/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT179 (i+1))
      = (∑ i ∈ Finset.range 230, stT179 (i+1)) + stT179 231 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 230
    simpa using h
  have hprev := st179_p230
  have hstep := st179_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p232 : ((7031533381843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT179 (i+1))
      = (∑ i ∈ Finset.range 231, stT179 (i+1)) + stT179 232 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 231
    simpa using h
  have hprev := st179_p231
  have hstep := st179_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p233 : ((3392014636463/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT179 (i+1))
      = (∑ i ∈ Finset.range 232, stT179 (i+1)) + stT179 233 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 232
    simpa using h
  have hprev := st179_p232
  have hstep := st179_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p234 : ((12915198496409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT179 (i+1))
      = (∑ i ∈ Finset.range 233, stT179 (i+1)) + stT179 234 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 233
    simpa using h
  have hprev := st179_p233
  have hstep := st179_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p235 : ((1558506224803/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT179 (i+1))
      = (∑ i ∈ Finset.range 234, stT179 (i+1)) + stT179 235 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 234
    simpa using h
  have hprev := st179_p234
  have hstep := st179_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p236 : ((1558902080123/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT179 (i+1))
      = (∑ i ∈ Finset.range 235, stT179 (i+1)) + stT179 236 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 235
    simpa using h
  have hprev := st179_p235
  have hstep := st179_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p237 : ((12919523831593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT179 (i+1))
      = (∑ i ∈ Finset.range 236, stT179 (i+1)) + stT179 237 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 236
    simpa using h
  have hprev := st179_p236
  have hstep := st179_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p238 : ((271334040453/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT179 (i+1))
      = (∑ i ∈ Finset.range 237, stT179 (i+1)) + stT179 238 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 237
    simpa using h
  have hprev := st179_p237
  have hstep := st179_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p239 : ((1406340212913/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT179 (i+1))
      = (∑ i ∈ Finset.range 238, stT179 (i+1)) + stT179 239 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 238
    simpa using h
  have hprev := st179_p238
  have hstep := st179_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p240 : ((1768237564839/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT179 (i+1))
      = (∑ i ∈ Finset.range 239, stT179 (i+1)) + stT179 240 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 239
    simpa using h
  have hprev := st179_p239
  have hstep := st179_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p241 : ((1377365120661/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT179 (i+1))
      = (∑ i ∈ Finset.range 240, stT179 (i+1)) + stT179 241 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 240
    simpa using h
  have hprev := st179_p240
  have hstep := st179_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p242 : ((2629078395657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT179 (i+1))
      = (∑ i ∈ Finset.range 241, stT179 (i+1)) + stT179 242 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 241
    simpa using h
  have hprev := st179_p241
  have hstep := st179_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p243 : ((12590133089723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT179 (i+1))
      = (∑ i ∈ Finset.range 242, stT179 (i+1)) + stT179 243 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 242
    simpa using h
  have hprev := st179_p242
  have hstep := st179_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p244 : ((6197082069409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT179 (i+1))
      = (∑ i ∈ Finset.range 243, stT179 (i+1)) + stT179 244 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 243
    simpa using h
  have hprev := st179_p243
  have hstep := st179_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p245 : ((6327625199679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT179 (i+1))
      = (∑ i ∈ Finset.range 244, stT179 (i+1)) + stT179 245 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 244
    simpa using h
  have hprev := st179_p244
  have hstep := st179_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p246 : ((6618610423047/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT179 (i+1))
      = (∑ i ∈ Finset.range 245, stT179 (i+1)) + stT179 246 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 245
    simpa using h
  have hprev := st179_p245
  have hstep := st179_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p247 : ((6922001132933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT179 (i+1))
      = (∑ i ∈ Finset.range 246, stT179 (i+1)) + stT179 247 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 246
    simpa using h
  have hprev := st179_p246
  have hstep := st179_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p248 : ((7085772712933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT179 (i+1))
      = (∑ i ∈ Finset.range 247, stT179 (i+1)) + stT179 248 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 247
    simpa using h
  have hprev := st179_p247
  have hstep := st179_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p249 : ((14059120709691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT179 (i+1))
      = (∑ i ∈ Finset.range 248, stT179 (i+1)) + stT179 249 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 248
    simpa using h
  have hprev := st179_p248
  have hstep := st179_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_p250 : ((13565346499091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT179 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT179 (i+1))
      = (∑ i ∈ Finset.range 249, stT179 (i+1)) + stT179 250 := by
    have h := Finset.sum_range_succ (fun i => stT179 (i+1)) 249
    simpa using h
  have hprev := st179_p249
  have hstep := st179_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st179_s250 :
    |Real.sin (((179 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))
      - ((624937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1233271/2000000) (δ := 9129/1000000000) (ψ := -4681/8000) 179 157
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 179`** (evaluated boundary). -/
theorem station_179_sign : hardyG ((((179:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 179 250 (by norm_num) (by norm_num)
    ((-4681/8000 : ℚ) : ℝ)
  have hchain := st179_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT179 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((179 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-4681/8000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st179_c250
  have hsinb := abs_le.mp st179_s250
  have hbdy_lo : ((-17626921948097/320412500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((179 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-4681/8000 : ℚ) : ℝ))) / 2
          - ((((179:ℕ)):ℝ))
            * Real.sin (((179 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-4681/8000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((179:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((179:ℝ) * Real.log (250:ℝ) - ((-4681/8000 : ℚ) : ℝ))) / 2
        - ((179:ℝ)) * Real.sin ((179:ℝ) * Real.log (250:ℝ) - ((-4681/8000 : ℚ) : ℝ))
        ≥ ((-222964721/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((179:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-222964721/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-222964721/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-222964721/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((179:ℕ)):ℝ))+1) * (((((179:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((22580971853/31250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((13565346499091/10000000000000 : ℚ) : ℝ) + ((-17626921948097/320412500000000 : ℚ) : ℝ)
      - ((22580971853/31250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-4681/8000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((179:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-4681/8000 : ℚ) : ℝ)
        * (riemannZeta (line ((((179:ℕ)):ℝ)))).re
      - Real.sin ((-4681/8000 : ℚ) : ℝ)
        * (riemannZeta (line ((((179:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((179:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((179:ℕ)):ℝ))
      = (((((179:ℕ)):ℝ)) * (Real.log ((((179:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((179:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_179
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
  have hθwin : |(((-4681/8000 : ℚ) : ℝ) + ((34:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((179:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((179:ℕ)):ℝ)))
    (φ := ((-4681/8000 : ℚ) : ℝ) + ((34:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-4681/8000 : ℚ) : ℝ) + ((34:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-4681/8000 : ℚ)) : ℝ) - Real.pi) + ((34:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-4681/8000 : ℚ)) : ℝ) - Real.pi) 34).1,
    (cos_sin_shift ((((-4681/8000 : ℚ)) : ℝ) - Real.pi) 34).2]
  exact cos_sin_flip ((-4681/8000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_179_sign
end AxiomAudit
