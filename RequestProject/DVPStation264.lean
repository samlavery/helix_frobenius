import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 264` (rung-280.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT264 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((264 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-29637/125000 : ℚ) : ℝ))

theorem st264_c1 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((121503/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29637/500000) (δ := 1/1000000000) (ψ := -29637/125000) 264 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t1 : ((485987/500000 : ℚ) : ℝ) ≤ stT264 1 := by
  have hc : ((485987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((485987/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((485987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c2 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((16473/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 634731/2500000) (δ := 13293/1000000000) (ψ := -29637/125000) 264 29
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t2 : ((1863530210381/5000000000000 : ℚ) : ℝ) ≤ stT264 2 := by
  have hc : ((263543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1863530210381/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((263543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c3 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((64163/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622103/2000000) (δ := 3333/250000000) (ψ := -29637/125000) 264 46
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t3 : ((185193736903/1000000000000 : ℚ) : ℝ) ≤ stT264 3 := by
  have hc : ((64153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185193736903/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((64153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c4 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-22141/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4485141/10000000) (δ := 2677/200000000) (ψ := -29637/125000) 264 58
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t4 : ((-55365011073/500000000000 : ℚ) : ℝ) ≤ stT264 4 := by
  have hc : ((-11073/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55365011073/500000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-11073/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c5 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-264359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1063943/2000000) (δ := 1329/100000000) (ψ := -29637/125000) 264 68
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t5 : ((-2309299227/9765625000 : ℚ) : ℝ) ≤ stT264 5 := by
  have hc : ((-8262/15625 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2309299227/9765625000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-8262/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c6 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-6823/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1264183/2500000) (δ := 331/25000000) (ψ := -29637/125000) 264 75
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t6 : ((-891455070363/5000000000000 : ℚ) : ℝ) ≤ stT264 6 := by
  have hc : ((-218361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-891455070363/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-218361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c7 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((151089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3159549/10000000) (δ := 13213/1000000000) (ψ := -29637/125000) 264 82
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t7 : ((17842754413/156250000000 : ℚ) : ℝ) ≤ stT264 7 := by
  have hc : ((18883/62500 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17842754413/156250000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((18883/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c8 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-421207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6431359/10000000) (δ := 6663/500000000) (ψ := -29637/125000) 264 87
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t8 : ((-46540001809/156250000000 : ℚ) : ℝ) ≤ stT264 8 := by
  have hc : ((-26327/31250 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46540001809/156250000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-26327/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c9 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-629207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2814161/5000000) (δ := 13341/1000000000) (ψ := -29637/125000) 264 92
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t9 : ((-1048761876419/5000000000000 : ℚ) : ℝ) ≤ stT264 9 := by
  have hc : ((-629257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1048761876419/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-629257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c10 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((219567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -843391/2500000) (δ := 2641/200000000) (ψ := -29637/125000) 264 97
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t10 : ((694173560209/10000000000000 : ℚ) : ℝ) ≤ stT264 10 := by
  have hc : ((219517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((694173560209/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((219517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c11 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((24791/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -660137/2000000) (δ := 13227/1000000000) (ψ := -29637/125000) 264 101
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t11 : ((37366295409/500000000000 : ℚ) : ℝ) ≤ stT264 11 := by
  have hc : ((12393/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37366295409/500000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((12393/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c12 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-942617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7002949/10000000) (δ := 2651/200000000) (ψ := -29637/125000) 264 104
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t12 : ((-85038932737/312500000000 : ℚ) : ℝ) ≤ stT264 12 := by
  have hc : ((-942667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85038932737/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-942667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c13 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((362089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1500361/5000000) (δ := 6613/500000000) (ψ := -29637/125000) 264 108
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t13 : ((2008230333/20000000000 : ℚ) : ℝ) ≤ stT264 13 := by
  have hc : ((362039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2008230333/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((362039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c14 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((22113/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -303333/2500000) (δ := 2661/200000000) (ψ := -29637/125000) 264 111
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t14 : ((59096128391/250000000000 : ℚ) : ℝ) ≤ stT264 14 := by
  have hc : ((88447/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59096128391/250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((88447/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c15 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((86999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -700477/2500000) (δ := 13383/1000000000) (ψ := -29637/125000) 264 114
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t15 : ((56151138533/500000000000 : ℚ) : ℝ) ≤ stT264 15 := by
  have hc : ((86989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56151138533/500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((86989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c16 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-244537/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7330387/10000000) (δ := 6671/500000000) (ψ := -29637/125000) 264 117
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t16 : ((-1222747989099/5000000000000 : ℚ) : ℝ) ≤ stT264 16 := by
  have hc : ((-489099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1222747989099/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-489099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c17 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((874511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 632961/5000000) (δ := 13247/1000000000) (ψ := -29637/125000) 264 119
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t17 : ((530219808279/2500000000000 : ℚ) : ℝ) ≤ stT264 17 := by
  have hc : ((874461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((530219808279/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((874461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c18 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-993759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378727/500000) (δ := 1337/100000000) (ψ := -29637/125000) 264 121
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t18 : ((-2342430670607/10000000000000 : ℚ) : ℝ) ≤ stT264 18 := by
  have hc : ((-993809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2342430670607/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-993809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c19 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((4959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1932499/5000000) (δ := 3323/250000000) (ψ := -29637/125000) 264 124
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t19 : ((11353782993/2000000000000 : ℚ) : ℝ) ≤ stT264 19 := by
  have hc : ((4949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11353782993/2000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((4949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c20 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((420697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1427347/10000000) (δ := 13297/1000000000) (ψ := -29637/125000) 264 126
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t20 : ((14697668391/78125000000 : ℚ) : ℝ) ≤ stT264 20 := by
  have hc : ((13146/15625 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14697668391/78125000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((13146/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c21 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((483617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -641741/10000000) (δ := 333/25000000) (ψ := -29637/125000) 264 128
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t21 : ((65955238961/312500000000 : ℚ) : ℝ) ≤ stT264 21 := by
  have hc : ((60449/62500 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65955238961/312500000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((60449/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c22 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((214197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338617/2500000) (δ := 3317/250000000) (ψ := -29637/125000) 264 130
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t22 : ((913285706583/5000000000000 : ℚ) : ℝ) ≤ stT264 22 := by
  have hc : ((428369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((913285706583/5000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((428369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c23 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((12289/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1716103/5000000) (δ := 13349/1000000000) (ψ := -29637/125000) 264 132
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t23 : ((25617818541/625000000000 : ℚ) : ℝ) ≤ stT264 23 := by
  have hc : ((98287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25617818541/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((98287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c24 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-90557/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6758797/10000000) (δ := 13239/1000000000) (ψ := -29637/125000) 264 134
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t24 : ((-46214739501/250000000000 : ℚ) : ℝ) ≤ stT264 24 := by
  have hc : ((-45281/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46214739501/250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-45281/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c25 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-217749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55947/125000) (δ := 13271/1000000000) (ψ := -29637/125000) 264 135
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t25 : ((-435598217799/10000000000000 : ℚ) : ℝ) ≤ stT264 25 := by
  have hc : ((-217799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435598217799/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-217799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c26 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((912353/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -210901/2000000) (δ := 6659/500000000) (ψ := -29637/125000) 264 137
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t26 : ((1789173063783/10000000000000 : ℚ) : ℝ) ≤ stT264 26 := by
  have hc : ((912303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1789173063783/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((912303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c27 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-49659/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7561833/10000000) (δ := 13299/1000000000) (ψ := -29637/125000) 264 139
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t27 : ((-191147212823/1000000000000 : ℚ) : ℝ) ≤ stT264 27 := by
  have hc : ((-99323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191147212823/1000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-99323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c28 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((957337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 146577/2000000) (δ := 3349/250000000) (ψ := -29637/125000) 264 140
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t28 : ((904551016457/5000000000000 : ℚ) : ℝ) ≤ stT264 28 := by
  have hc : ((957287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((904551016457/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((957287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c29 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-991237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7522783/10000000) (δ := 13221/1000000000) (ψ := -29637/125000) 264 142
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t29 : ((-920387179899/5000000000000 : ℚ) : ℝ) ≤ stT264 29 := by
  have hc : ((-991287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-920387179899/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-991287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c30 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((29437/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213939/2500000) (δ := 833/62500000) (ψ := -29637/125000) 264 143
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t30 : ((859863761547/5000000000000 : ℚ) : ℝ) ≤ stT264 30 := by
  have hc : ((470967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((859863761547/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((470967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c31 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-444171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2538807/5000000) (δ := 1671/125000000) (ψ := -29637/125000) 264 144
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t31 : ((-398922451967/5000000000000 : ℚ) : ℝ) ≤ stT264 31 := by
  have hc : ((-444221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-398922451967/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-444221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c32 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-68803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -538417/1000000) (δ := 53/4000000) (ψ := -29637/125000) 264 146
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t32 : ((-486554885779/5000000000000 : ℚ) : ℝ) ≤ stT264 32 := by
  have hc : ((-275237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-486554885779/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-275237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c33 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((118921/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -782877/10000000) (δ := 13357/1000000000) (ψ := -29637/125000) 264 147
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t33 : ((103501971423/625000000000 : ℚ) : ℝ) ≤ stT264 33 := by
  have hc : ((475659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103501971423/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((475659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c34 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((14103/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3212139/10000000) (δ := 13339/1000000000) (ψ := -29637/125000) 264 148
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t34 : ((9672858397/200000000000 : ℚ) : ℝ) ≤ stT264 34 := by
  have hc : ((28201/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9672858397/200000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((28201/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c35 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-883637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3317963/5000000) (δ := 827/62500000) (ψ := -29637/125000) 264 149
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t35 : ((-1493704089283/10000000000000 : ℚ) : ℝ) ≤ stT264 35 := by
  have hc : ((-883687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1493704089283/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-883687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c36 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-39293/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3093603/5000000) (δ := 6693/500000000) (ψ := -29637/125000) 264 151
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t36 : ((-130985026197/1000000000000 : ℚ) : ℝ) ≤ stT264 36 := by
  have hc : ((-78591/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130985026197/1000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-78591/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c37 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((1439/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381183/1000000) (δ := 1331/100000000) (ψ := -29637/125000) 264 152
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t37 : ((37810103011/5000000000000 : ℚ) : ℝ) ≤ stT264 37 := by
  have hc : ((22999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37810103011/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((22999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c38 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((17991/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1918781/10000000) (δ := 13203/1000000000) (ψ := -29637/125000) 264 153
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t38 : ((58366448613/500000000000 : ℚ) : ℝ) ≤ stT264 38 := by
  have hc : ((71959/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58366448613/500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((71959/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c39 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((981401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241457/5000000) (δ := 13307/1000000000) (ψ := -29637/125000) 264 154
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t39 : ((1571418710631/10000000000000 : ℚ) : ℝ) ≤ stT264 39 := by
  have hc : ((981351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1571418710631/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((981351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c40 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((978539/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51887/1000000) (δ := 13389/1000000000) (ψ := -29637/125000) 264 155
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t40 : ((773563070241/5000000000000 : ℚ) : ℝ) ≤ stT264 40 := by
  have hc : ((978489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((773563070241/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((978489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c41 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((45169/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1108023/10000000) (δ := 13281/1000000000) (ψ := -29637/125000) 264 156
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t41 : ((141076388421/1000000000000 : ℚ) : ℝ) ≤ stT264 41 := by
  have hc : ((90333/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141076388421/1000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((90333/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c42 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((54183/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 326119/2500000) (δ := 13229/1000000000) (ψ := -29637/125000) 264 157
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t42 : ((668810680487/5000000000000 : ℚ) : ℝ) ≤ stT264 42 := by
  have hc : ((433439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((668810680487/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((433439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c43 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((900161/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1126643/10000000) (δ := 1667/125000000) (ψ := -29637/125000) 264 158
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t43 : ((274531154667/2000000000000 : ℚ) : ℝ) ≤ stT264 43 := by
  have hc : ((900111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274531154667/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((900111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c44 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((972117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 591749/10000000) (δ := 167/12500000) (ψ := -29637/125000) 264 159
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t44 : ((366361359563/2500000000000 : ℚ) : ℝ) ≤ stT264 44 := by
  have hc : ((972067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((366361359563/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((972067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c45 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((993547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142083/5000000) (δ := 13253/1000000000) (ψ := -29637/125000) 264 160
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t45 : ((1481016906367/10000000000000 : ℚ) : ℝ) ≤ stT264 45 := by
  have hc : ((993497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1481016906367/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((993497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c46 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((103559/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297211/2000000) (δ := 13257/1000000000) (ψ := -29637/125000) 264 161
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t46 : ((610720568409/5000000000000 : ℚ) : ℝ) ≤ stT264 46 := by
  have hc : ((414211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((610720568409/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((414211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c47 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((36241/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149993/500000) (δ := 2673/200000000) (ψ := -29637/125000) 264 162
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t47 : ((13213901291/250000000000 : ℚ) : ℝ) ≤ stT264 47 := by
  have hc : ((9059/25000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13213901291/250000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((9059/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c48 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-173437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -240629/500000) (δ := 13331/1000000000) (ψ := -29637/125000) 264 163
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t48 : ((-7824090241/156250000000 : ℚ) : ℝ) ≤ stT264 48 := by
  have hc : ((-86731/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7824090241/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-86731/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c49 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-929831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6911871/10000000) (δ := 1653/125000000) (ψ := -29637/125000) 264 164
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t49 : ((-332100489983/2500000000000 : ℚ) : ℝ) ≤ stT264 49 := by
  have hc : ((-929881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332100489983/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-929881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c50 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-420193/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6421977/10000000) (δ := 1653/125000000) (ψ := -29637/125000) 264 164
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t50 : ((-148569544663/1250000000000 : ℚ) : ℝ) ≤ stT264 50 := by
  have hc : ((-210109/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148569544663/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-210109/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c51 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((57273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 378373/1000000) (δ := 6643/500000000) (ψ := -29637/125000) 264 165
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t51 : ((2003205561/250000000000 : ℚ) : ℝ) ≤ stT264 51 := by
  have hc : ((57223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2003205561/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((57223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c52 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((937059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 891713/10000000) (δ := 13393/1000000000) (ψ := -29637/125000) 264 166
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t52 : ((5197588923/40000000000 : ℚ) : ℝ) ≤ stT264 52 := by
  have hc : ((937009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5197588923/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((937009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c53 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((623351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2244439/10000000) (δ := 13303/1000000000) (ψ := -29637/125000) 264 167
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t53 : ((171233874021/2000000000000 : ℚ) : ℝ) ≤ stT264 53 := by
  have hc : ((623301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171233874021/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((623301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c54 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-625249/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43872/78125) (δ := 1651/125000000) (ψ := -29637/125000) 264 168
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t54 : ((-212731096893/2500000000000 : ℚ) : ℝ) ≤ stT264 54 := by
  have hc : ((-625299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212731096893/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-625299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c55 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-855813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 649479/1000000) (δ := 1651/125000000) (ψ := -29637/125000) 264 168
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t55 : ((-2885114173/25000000000 : ℚ) : ℝ) ≤ stT264 55 := by
  have hc : ((-855863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2885114173/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-855863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c56 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((478707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2679037/10000000) (δ := 2663/200000000) (ψ := -29637/125000) 264 169
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t56 : ((319816110521/5000000000000 : ℚ) : ℝ) ≤ stT264 56 := by
  have hc : ((478657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((319816110521/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((478657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c57 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((429143/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1347191/10000000) (δ := 13381/1000000000) (ψ := -29637/125000) 264 170
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t57 : ((71047565347/625000000000 : ℚ) : ℝ) ≤ stT264 57 := by
  have hc : ((214559/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71047565347/625000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((214559/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c58 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-612983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2788283/5000000) (δ := 6637/500000000) (ψ := -29637/125000) 264 171
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t58 : ((-160990435229/2000000000000 : ℚ) : ℝ) ≤ stT264 58 := by
  have hc : ((-613033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160990435229/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-613033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c59 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-65297/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2852869/5000000) (δ := 6637/500000000) (ψ := -29637/125000) 264 171
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t59 : ((-4250801039/50000000000 : ℚ) : ℝ) ≤ stT264 59 := by
  have hc : ((-32651/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4250801039/50000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-32651/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c60 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((90637/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1090461/10000000) (δ := 3309/250000000) (ψ := -29637/125000) 264 172
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t60 : ((7312835513/62500000000 : ℚ) : ℝ) ≤ stT264 60 := by
  have hc : ((11329/12500 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7312835513/62500000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((11329/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c61 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((87419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -927041/2500000) (δ := 417/31250000) (ψ := -29637/125000) 264 173
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t61 : ((6991529487/625000000000 : ℚ) : ℝ) ≤ stT264 61 := by
  have hc : ((87369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6991529487/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((87369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c62 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-236341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3511883/5000000) (δ := 417/31250000) (ψ := -29637/125000) 264 173
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t62 : ((-300169417707/2500000000000 : ℚ) : ℝ) ≤ stT264 62 := by
  have hc : ((-472707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300169417707/2500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-472707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c63 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((365699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 938033/5000000) (δ := 1669/125000000) (ψ := -29637/125000) 264 174
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t63 : ((230352862397/2500000000000 : ℚ) : ℝ) ≤ stT264 63 := by
  have hc : ((182837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230352862397/2500000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((182837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c64 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((24293/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3438019/10000000) (δ := 2649/200000000) (ψ := -29637/125000) 264 175
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t64 : ((97147/4000000 : ℚ) : ℝ) ≤ stT264 64 := by
  have hc : ((97147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97147/4000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((97147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c65 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-911577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6794753/10000000) (δ := 2649/200000000) (ψ := -29637/125000) 264 175
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t65 : ((-282683681549/2500000000000 : ℚ) : ℝ) ≤ stT264 65 := by
  have hc : ((-911627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282683681549/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-911627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c66 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((893671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58167/500000) (δ := 2653/200000000) (ψ := -29637/125000) 264 176
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t66 : ((549985299797/5000000000000 : ℚ) : ℝ) ≤ stT264 66 := by
  have hc : ((893621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((549985299797/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((893621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c67 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-273517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4619609/10000000) (δ := 3343/250000000) (ψ := -29637/125000) 264 177
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t67 : ((-66843087213/2000000000000 : ℚ) : ℝ) ≤ stT264 67 := by
  have hc : ((-273567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66843087213/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-273567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c68 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-472871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5158357/10000000) (δ := 3343/250000000) (ψ := -29637/125000) 264 177
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t68 : ((-573501365359/10000000000000 : ℚ) : ℝ) ≤ stT264 68 := by
  have hc : ((-472921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573501365359/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-472921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c69 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((233463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -914399/10000000) (δ := 3331/250000000) (ψ := -29637/125000) 264 178
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t69 : ((281041252029/2500000000000 : ℚ) : ℝ) ≤ stT264 69 := by
  have hc : ((466901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((281041252029/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((466901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c70 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-957881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -356291/500000) (δ := 413/31250000) (ψ := -29637/125000) 264 179
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t70 : ((-1144946911199/10000000000000 : ℚ) : ℝ) ≤ stT264 70 := by
  have hc : ((-957931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1144946911199/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-957931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c71 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((312991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139751/625000) (δ := 413/31250000) (ψ := -29637/125000) 264 179
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t71 : ((185711051223/2500000000000 : ℚ) : ℝ) ≤ stT264 71 := by
  have hc : ((156483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185711051223/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((156483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c72 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-125269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4240989/10000000) (δ := 6647/500000000) (ψ := -29637/125000) 264 180
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t72 : ((-9230621583/625000000000 : ℚ) : ℝ) ≤ stT264 72 := by
  have hc : ((-125319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9230621583/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-125319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c73 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-73113/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4862589/10000000) (δ := 6647/500000000) (ψ := -29637/125000) 264 180
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t73 : ((-21396009169/500000000000 : ℚ) : ℝ) ≤ stT264 73 := by
  have hc : ((-73123/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21396009169/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-73123/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c74 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((29369/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -932839/5000000) (δ := 13401/1000000000) (ψ := -29637/125000) 264 181
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t74 : ((8534608173/100000000000 : ℚ) : ℝ) ≤ stT264 74 := by
  have hc : ((29367/40000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8534608173/100000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((29367/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c75 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-941357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 218549/312500) (δ := 13401/1000000000) (ψ := -29637/125000) 264 181
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t75 : ((-1087043604307/10000000000000 : ℚ) : ℝ) ≤ stT264 75 := by
  have hc : ((-941407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1087043604307/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-941407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c76 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((49997/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6859/2500000) (δ := 2659/200000000) (ψ := -29637/125000) 264 182
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t76 : ((57347591071/500000000000 : ℚ) : ℝ) ≤ stT264 76 := by
  have hc : ((99989/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57347591071/500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((99989/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c77 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-59319/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7052941/10000000) (δ := 2643/200000000) (ψ := -29637/125000) 264 183
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t77 : ((-270415398331/2500000000000 : ℚ) : ℝ) ≤ stT264 77 := by
  have hc : ((-474577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270415398331/2500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-474577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c78 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((166707/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1463303/10000000) (δ := 2643/200000000) (ψ := -29637/125000) 264 183
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t78 : ((188747179069/2000000000000 : ℚ) : ℝ) ≤ stT264 78 := by
  have hc : ((166697/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188747179069/2000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((166697/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c79 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-138359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -145923/250000) (δ := 13323/1000000000) (ψ := -29637/125000) 264 184
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t79 : ((-4864915671/62500000000 : ℚ) : ℝ) ≤ stT264 79 := by
  have hc : ((-138369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4864915671/62500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-138369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c80 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((69/125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38517/156250) (δ := 13323/1000000000) (ψ := -29637/125000) 264 184
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t80 : ((12341966287/200000000000 : ℚ) : ℝ) ≤ stT264 80 := by
  have hc : ((11039/20000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12341966287/200000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((11039/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c81 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-86419/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2522013/5000000) (δ := 13373/1000000000) (ψ := -29637/125000) 264 185
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t81 : ((-12004037381/250000000000 : ℚ) : ℝ) ≤ stT264 81 := by
  have hc : ((-86429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12004037381/250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-86429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c82 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((342053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19089/62500) (δ := 13373/1000000000) (ψ := -29637/125000) 264 185
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t82 : ((75535808589/2000000000000 : ℚ) : ℝ) ≤ stT264 82 := by
  have hc : ((342003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75535808589/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((342003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c83 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-286569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4653599/10000000) (δ := 6633/500000000) (ψ := -29637/125000) 264 186
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t83 : ((-314605339017/10000000000000 : ℚ) : ℝ) ≤ stT264 83 := by
  have hc : ((-286619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-314605339017/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-286619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c84 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((66811/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162533/500000) (δ := 13233/500000000) (ψ := -29637/125000) 264 186
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t84 : ((145766217133/5000000000000 : ℚ) : ℝ) ≤ stT264 84 := by
  have hc : ((133597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145766217133/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((133597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c85 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-8871/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2323283/5000000) (δ := 3311/250000000) (ψ := -29637/125000) 264 187
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t85 : ((-153978424533/5000000000000 : ℚ) : ℝ) ≤ stT264 85 := by
  have hc : ((-141961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153978424533/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-141961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c86 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((335069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1536397/5000000) (δ := 3311/250000000) (ψ := -29637/125000) 264 187
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t86 : ((361260033213/10000000000000 : ℚ) : ℝ) ≤ stT264 86 := by
  have hc : ((335019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361260033213/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((335019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c87 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-104489/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200199/400000) (δ := 13351/1000000000) (ψ := -29637/125000) 264 188
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t87 : ((-224074833339/5000000000000 : ℚ) : ℝ) ≤ stT264 87 := by
  have hc : ((-209003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-224074833339/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-209003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c88 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((527461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2537967/10000000) (δ := 13351/1000000000) (ψ := -29637/125000) 264 188
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t88 : ((562221708233/10000000000000 : ℚ) : ℝ) ≤ stT264 88 := by
  have hc : ((527411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((562221708233/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((527411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c89 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-163741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5712327/10000000) (δ := 2669/200000000) (ψ := -29637/125000) 264 189
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t89 : ((-173578382493/2500000000000 : ℚ) : ℝ) ≤ stT264 89 := by
  have hc : ((-327507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173578382493/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-327507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c90 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((196757/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1662051/10000000) (δ := 2669/200000000) (ψ := -29637/125000) 264 189
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t90 : ((103693401747/1250000000000 : ℚ) : ℝ) ≤ stT264 90 := by
  have hc : ((393489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103693401747/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((393489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c91 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-452293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6753011/10000000) (δ := 26437/1000000000) (ψ := -29637/125000) 264 190
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t91 : ((-47415817463/500000000000 : ℚ) : ℝ) ≤ stT264 91 := by
  have hc : ((-226159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47415817463/500000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-226159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c92 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((245777/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230081/5000000) (δ := 13237/1000000000) (ψ := -29637/125000) 264 190
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t92 : ((128113593147/1250000000000 : ℚ) : ℝ) ≤ stT264 92 := by
  have hc : ((491529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128113593147/1250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((491529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c93 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-497327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1898839/2500000) (δ := 13237/1000000000) (ψ := -29637/125000) 264 190
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t93 : ((-8058283611/78125000000 : ℚ) : ℝ) ≤ stT264 93 := by
  have hc : ((-62169/62500 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8058283611/78125000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-62169/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c94 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((912483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053709/10000000) (δ := 13273/1000000000) (ψ := -29637/125000) 264 191
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t94 : ((941102557293/10000000000000 : ℚ) : ℝ) ≤ stT264 94 := by
  have hc : ((912433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((941102557293/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((912433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c95 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-718327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5930477/10000000) (δ := 13273/1000000000) (ψ := -29637/125000) 264 191
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t95 : ((-737039716083/10000000000000 : ℚ) : ℝ) ≤ stT264 95 := by
  have hc : ((-718377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-737039716083/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-718377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c96 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((82323/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -716607/2500000) (δ := 669/50000000) (ψ := -29637/125000) 264 192
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t96 : ((4200514703/100000000000 : ℚ) : ℝ) ≤ stT264 96 := by
  have hc : ((82313/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4200514703/100000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((82313/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c97 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-18411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 198651/500000) (δ := 669/50000000) (ψ := -29637/125000) 264 192
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t97 : ((-18744320967/10000000000000 : ℚ) : ℝ) ≤ stT264 97 := by
  have hc : ((-18461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18744320967/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-18461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c98 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-12613/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2482827/5000000) (δ := 3329/250000000) (ψ := -29637/125000) 264 193
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t98 : ((-203882210449/5000000000000 : ℚ) : ℝ) ≤ stT264 98 := by
  have hc : ((-201833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-203882210449/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-201833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c99 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((96089/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173493/1000000) (δ := 3329/250000000) (ψ := -29637/125000) 264 193
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t99 : ((386266875247/5000000000000 : ℚ) : ℝ) ≤ stT264 99 := by
  have hc : ((384331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386266875247/5000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((384331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c100 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-978927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1467967/2000000) (δ := 13209/1000000000) (ψ := -29637/125000) 264 194
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t100 : ((-978977/10000000 : ℚ) : ℝ) ≤ stT264 100 := by
  have hc : ((-978977/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-978977/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-978977/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c101 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((95263/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772571/10000000) (δ := 13209/1000000000) (ψ := -29637/125000) 264 194
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t101 : ((47392617273/500000000000 : ℚ) : ℝ) ≤ stT264 101 := by
  have hc : ((47629/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47392617273/500000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((47629/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c102 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-660273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5729947/10000000) (δ := 13209/1000000000) (ψ := -29637/125000) 264 194
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t102 : ((-163454374451/2500000000000 : ℚ) : ℝ) ≤ stT264 102 := by
  have hc : ((-660323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163454374451/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-660323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c103 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((77289/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353899/1000000) (δ := 6651/500000000) (ψ := -29637/125000) 264 195
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t103 : ((4758153741/312500000000 : ℚ) : ℝ) ≤ stT264 103 := by
  have hc : ((4829/31250 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4758153741/312500000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((4829/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c104 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((211/500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 354733/1250000) (δ := 6651/500000000) (ψ := -29637/125000) 264 195
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t104 : ((413755731/10000000000 : ℚ) : ℝ) ≤ stT264 104 := by
  have hc : ((8439/20000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((413755731/10000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((8439/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c105 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-867869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -655423/1000000) (δ := 6697/500000000) (ψ := -29637/125000) 264 196
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t105 : ((-847003020019/10000000000000 : ℚ) : ℝ) ≤ stT264 105 := by
  have hc : ((-867919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-847003020019/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-867919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c106 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((99289/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18643/625000) (δ := 6697/500000000) (ψ := -29637/125000) 264 196
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t106 : ((4821652997/50000000000 : ℚ) : ℝ) ≤ stT264 106 := by
  have hc : ((24821/25000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4821652997/50000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((24821/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c107 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-141901/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294949/500000) (δ := 6697/500000000) (ψ := -29637/125000) 264 196
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t107 : ((-137190614407/2000000000000 : ℚ) : ℝ) ≤ stT264 107 := by
  have hc : ((-141911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137190614407/2000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-141911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c108 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((20571/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3669399/10000000) (δ := 13287/1000000000) (ψ := -29637/125000) 264 197
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t108 : ((79139289/8000000000 : ℚ) : ℝ) ≤ stT264 108 := by
  have hc : ((20561/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79139289/8000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((20561/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c109 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((569069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2413557/10000000) (δ := 13287/1000000000) (ψ := -29637/125000) 264 197
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t109 : ((272510596347/5000000000000 : ℚ) : ℝ) ≤ stT264 109 := by
  have hc : ((569019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272510596347/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((569019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c110 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-972559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1816739/2500000) (δ := 13223/1000000000) (ψ := -29637/125000) 264 198
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t110 : ((-927346694967/10000000000000 : ℚ) : ℝ) ≤ stT264 110 := by
  have hc : ((-972609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-927346694967/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-972609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c111 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((173801/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -647011/5000000) (δ := 13223/1000000000) (ψ := -29637/125000) 264 198
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t111 : ((164954944187/2000000000000 : ℚ) : ℝ) ≤ stT264 111 := by
  have hc : ((173791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164954944187/2000000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((173791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c112 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-34461/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2312627/5000000) (δ := 13223/1000000000) (ψ := -29637/125000) 264 198
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t112 : ((-8142129533/312500000000 : ℚ) : ℝ) ≤ stT264 112 := by
  have hc : ((-137869/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8142129533/312500000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-137869/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c113 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-493049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5215969/10000000) (δ := 1333/100000000) (ψ := -29637/125000) 264 199
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t113 : ((-463868584379/10000000000000 : ℚ) : ℝ) ≤ stT264 113 := by
  have hc : ((-493099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-463868584379/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-493099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c114 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((97143/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 599027/10000000) (δ := 1333/100000000) (ψ := -29637/125000) 264 199
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t114 : ((9097799373/100000000000 : ℚ) : ℝ) ≤ stT264 114 := by
  have hc : ((48569/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9097799373/100000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((48569/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c115 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-206857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6363269/10000000) (δ := 1333/100000000) (ψ := -29637/125000) 264 199
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t115 : ((-77162737239/1000000000000 : ℚ) : ℝ) ≤ stT264 115 := by
  have hc : ((-413739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77162737239/1000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-413739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c116 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((7397/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726083/2000000) (δ := 6683/500000000) (ψ := -29637/125000) 264 200
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t116 : ((13730070969/1250000000000 : ℚ) : ℝ) ≤ stT264 116 := by
  have hc : ((59151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13730070969/1250000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((59151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c117 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((686627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2034893/10000000) (δ := 6683/500000000) (ψ := -29637/125000) 264 200
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t117 : ((1269480873/20000000000 : ℚ) : ℝ) ≤ stT264 117 := by
  have hc : ((686577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1269480873/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((686577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c118 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-996737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1530391/2000000) (δ := 6683/500000000) (ψ := -29637/125000) 264 200
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t118 : ((-36704687701/400000000000 : ℚ) : ℝ) ≤ stT264 118 := by
  have hc : ((-996787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36704687701/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-996787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c119 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((68109/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -777/3125) (δ := 6629/500000000) (ψ := -29637/125000) 264 201
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t119 : ((124859309439/2500000000000 : ℚ) : ℝ) ≤ stT264 119 := by
  have hc : ((272411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124859309439/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((272411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c120 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((69729/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1518339/5000000) (δ := 6629/500000000) (ψ := -29637/125000) 264 201
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t120 : ((6364438353/200000000000 : ℚ) : ℝ) ≤ stT264 120 := by
  have hc : ((69719/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6364438353/200000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((69719/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c121 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-241341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7194077/10000000) (δ := 3313/250000000) (ψ := -29637/125000) 264 202
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t121 : ((-438824589337/5000000000000 : ℚ) : ℝ) ≤ stT264 121 := by
  have hc : ((-482707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438824589337/5000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-482707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c122 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((152351/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1761947/10000000) (δ := 3313/250000000) (ψ := -29637/125000) 264 202
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t122 : ((137922990737/2000000000000 : ℚ) : ℝ) ≤ stT264 122 := by
  have hc : ((152341/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137922990737/2000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((152341/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c123 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((120173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3625831/10000000) (δ := 3313/250000000) (ψ := -29637/125000) 264 202
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t123 : ((108311185287/10000000000000 : ℚ) : ℝ) ≤ stT264 123 := by
  have hc : ((120123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108311185287/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((120123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c124 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-902007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -336899/500000) (δ := 13359/1000000000) (ψ := -29637/125000) 264 203
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t124 : ((-810071541539/10000000000000 : ℚ) : ℝ) ≤ stT264 124 := by
  have hc : ((-902057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-810071541539/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-902057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c125 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((2623/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179591/1250000) (δ := 13359/1000000000) (ψ := -29637/125000) 264 203
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t125 : ((75070152537/1000000000000 : ℚ) : ℝ) ≤ stT264 125 := by
  have hc : ((83931/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75070152537/1000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((83931/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c126 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((4187/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 955571/2500000) (δ := 13359/1000000000) (ψ := -29637/125000) 264 203
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t126 : ((186280917/50000000000 : ℚ) : ℝ) ≤ stT264 126 := by
  have hc : ((2091/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((186280917/50000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((2091/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c127 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-222407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3334157/5000000) (δ := 13337/1000000000) (ψ := -29637/125000) 264 204
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t127 : ((-394731000523/5000000000000 : ℚ) : ℝ) ≤ stT264 127 := by
  have hc : ((-444839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-394731000523/5000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-444839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c128 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((827183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -745901/5000000) (δ := 13337/1000000000) (ψ := -29637/125000) 264 204
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t128 : ((731088797439/10000000000000 : ℚ) : ℝ) ≤ stT264 128 := by
  have hc : ((827133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((731088797439/10000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((827133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c129 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((14097/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72889/200000) (δ := 13337/1000000000) (ψ := -29637/125000) 264 204
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t129 : ((992496067/100000000000 : ℚ) : ℝ) ≤ stT264 129 := by
  have hc : ((56363/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((992496067/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((56363/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c130 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-468859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6966993/10000000) (δ := 1323/100000000) (ψ := -29637/125000) 264 205
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t130 : ((-102809733039/1250000000000 : ℚ) : ℝ) ≤ stT264 130 := by
  have hc : ((-117221/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102809733039/1250000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-117221/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c131 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((722219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1909479/10000000) (δ := 1323/100000000) (ψ := -29637/125000) 264 205
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t131 : ((78870242997/1250000000000 : ℚ) : ℝ) ≤ stT264 131 := by
  have hc : ((722169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78870242997/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((722169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c132 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((160589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3109557/10000000) (δ := 1323/100000000) (ψ := -29637/125000) 264 205
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t132 : ((8734561177/312500000000 : ℚ) : ℝ) ≤ stT264 132 := by
  have hc : ((40141/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8734561177/312500000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((40141/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c133 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-3111/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3808627/5000000) (δ := 83/6250000) (ψ := -29637/125000) 264 206
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t133 : ((-8632687027/100000000000 : ℚ) : ℝ) ≤ stT264 133 := by
  have hc : ((-99557/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8632687027/100000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-99557/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c134 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((480677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106937/400000) (δ := 331/12500000) (ψ := -29637/125000) 264 206
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t134 : ((103799571309/2500000000000 : ℚ) : ℝ) ≤ stT264 134 := by
  have hc : ((480627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103799571309/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((480627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c135 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((313361/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1116821/5000000) (δ := 83/6250000) (ψ := -29637/125000) 264 206
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t135 : ((16854774277/312500000000 : ℚ) : ℝ) ≤ stT264 135 := by
  have hc : ((39167/62500 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16854774277/312500000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((39167/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c136 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-955399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1776127/2500000) (δ := 83/6250000) (ψ := -29637/125000) 264 206
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t136 : ((-819290829357/10000000000000 : ℚ) : ℝ) ≤ stT264 136 := by
  have hc : ((-955449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-819290829357/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-955449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c137 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((31731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3768229/10000000) (δ := 3347/250000000) (ψ := -29637/125000) 264 207
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t137 : ((13544121521/2500000000000 : ℚ) : ℝ) ≤ stT264 137 := by
  have hc : ((15853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13544121521/2500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((15853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c138 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((916041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1031753/10000000) (δ := 3347/250000000) (ψ := -29637/125000) 264 207
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t138 : ((97467854337/1250000000000 : ℚ) : ℝ) ≤ stT264 138 := by
  have hc : ((915991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97467854337/1250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((915991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c139 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-680221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5797151/10000000) (δ := 3347/250000000) (ψ := -29637/125000) 264 207
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t139 : ((-576998379219/10000000000000 : ℚ) : ℝ) ≤ stT264 139 := by
  have hc : ((-680271/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-576998379219/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-680271/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c140 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-240171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5179603/10000000) (δ := 3327/250000000) (ψ := -29637/125000) 264 208
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t140 : ((-10150142519/250000000000 : ℚ) : ℝ) ≤ stT264 140 := by
  have hc : ((-60049/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10150142519/250000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-60049/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c141 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((490731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482119/10000000) (δ := 3327/250000000) (ψ := -29637/125000) 264 208
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t141 : ((206624274303/2500000000000 : ℚ) : ℝ) ≤ stT264 141 := by
  have hc : ((245353/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((206624274303/2500000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((245353/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c142 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-637/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4182233/10000000) (δ := 3327/250000000) (ψ := -29637/125000) 264 208
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t142 : ((-4278569427/500000000000 : ℚ) : ℝ) ≤ stT264 142 := by
  have hc : ((-10197/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4278569427/500000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-10197/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c143 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-927193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3447057/5000000) (δ := 6601/500000000) (ψ := -29637/125000) 264 209
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t143 : ((-775400468049/10000000000000 : ℚ) : ℝ) ≤ stT264 143 := by
  have hc : ((-927243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-775400468049/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-927243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c144 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((303731/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1147419/5000000) (δ := 6601/500000000) (ψ := -29637/125000) 264 209
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t144 : ((126544116049/2500000000000 : ℚ) : ℝ) ≤ stT264 144 := by
  have hc : ((151853/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126544116049/2500000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((151853/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c145 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((307237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 568173/2500000) (δ := 6601/500000000) (ψ := -29637/125000) 264 209
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t145 : ((31890679281/625000000000 : ℚ) : ℝ) ≤ stT264 145 := by
  have hc : ((76803/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31890679281/625000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((76803/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c146 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-456937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3404403/5000000) (δ := 6601/500000000) (ψ := -29637/125000) 264 209
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t146 : ((-94546123243/1250000000000 : ℚ) : ℝ) ≤ stT264 146 := by
  have hc : ((-228481/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94546123243/1250000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-228481/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c147 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-11609/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4394063/10000000) (δ := 13309/1000000000) (ψ := -29637/125000) 264 210
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t147 : ((-76620237939/5000000000000 : ℚ) : ℝ) ≤ stT264 147 := by
  have hc : ((-92897/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76620237939/5000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-92897/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c148 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((999481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80539/10000000) (δ := 13309/1000000000) (ψ := -29637/125000) 264 210
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t148 : ((410763142707/5000000000000 : ℚ) : ℝ) ≤ stT264 148 := by
  have hc : ((999431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((410763142707/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((999431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c149 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-236947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 905009/2000000) (δ := 13309/1000000000) (ψ := -29637/125000) 264 210
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t149 : ((-6067360197/312500000000 : ℚ) : ℝ) ≤ stT264 149 := by
  have hc : ((-236997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6067360197/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-236997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c150 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-907167/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353649/2000000) (δ := 13387/1000000000) (ψ := -29637/125000) 264 211
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t150 : ((-740739958849/10000000000000 : ℚ) : ℝ) ≤ stT264 150 := by
  have hc : ((-907217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-740739958849/10000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-907217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c151 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((579139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2382809/10000000) (δ := 13387/1000000000) (ψ := -29637/125000) 264 211
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t151 : ((117813919783/2500000000000 : ℚ) : ℝ) ≤ stT264 151 := by
  have hc : ((579089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117813919783/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((579089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c152 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((176057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1973653/10000000) (δ := 13387/1000000000) (ψ := -29637/125000) 264 211
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t152 : ((285581852523/5000000000000 : ℚ) : ℝ) ≤ stT264 152 := by
  have hc : ((352089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285581852523/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((352089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c153 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-81331/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6301537/10000000) (δ := 13387/1000000000) (ψ := -29637/125000) 264 211
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t153 : ((-8219541651/125000000000 : ℚ) : ℝ) ≤ stT264 153 := by
  have hc : ((-10167/12500 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8219541651/125000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-10167/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c154 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-454573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1276681/2500000) (δ := 13279/1000000000) (ψ := -29637/125000) 264 212
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t154 : ((-366345669729/10000000000000 : ℚ) : ℝ) ≤ stT264 154 := by
  have hc : ((-454623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-366345669729/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-454623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c155 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((188951/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -417437/5000000) (δ := 13279/1000000000) (ψ := -29637/125000) 264 212
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t155 : ((151761001079/2000000000000 : ℚ) : ℝ) ≤ stT264 155 := by
  have hc : ((188941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((151761001079/2000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((188941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c156 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((205513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42619/125000) (δ := 13279/1000000000) (ψ := -29637/125000) 264 212
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t156 : ((257034213/15625000000 : ℚ) : ℝ) ≤ stT264 156 := by
  have hc : ((205463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257034213/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((205463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c157 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-995873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1906697/2500000) (δ := 13279/1000000000) (ψ := -29637/125000) 264 212
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t157 : ((-794833199301/10000000000000 : ℚ) : ℝ) ≤ stT264 157 := by
  have hc : ((-995923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-794833199301/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-995923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c158 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((2903/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3890703/10000000) (δ := 13231/1000000000) (ψ := -29637/125000) 264 213
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t158 : ((2301546401/2000000000000 : ℚ) : ℝ) ≤ stT264 158 := by
  have hc : ((2893/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2301546401/2000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((2893/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c159 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((248507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273369/10000000) (δ := 13231/1000000000) (ψ := -29637/125000) 264 213
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t159 : ((394137623439/5000000000000 : ℚ) : ℝ) ≤ stT264 159 := by
  have hc : ((496989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((394137623439/5000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((496989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c160 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-48129/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 882261/2000000) (δ := 13231/1000000000) (ψ := -29637/125000) 264 213
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t160 : ((-7611845131/500000000000 : ℚ) : ℝ) ≤ stT264 160 := by
  have hc : ((-96283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7611845131/500000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-96283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c161 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-24109/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449033/625000) (δ := 6669/500000000) (ψ := -29637/125000) 264 214
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t161 : ((-76006212951/1000000000000 : ℚ) : ℝ) ≤ stT264 161 := by
  have hc : ((-96441/100000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76006212951/1000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-96441/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c162 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((521/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193613/625000) (δ := 6669/500000000) (ψ := -29637/125000) 264 214
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t162 : ((5115916251/200000000000 : ℚ) : ℝ) ≤ stT264 162 := by
  have hc : ((13023/40000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5115916251/200000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((13023/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c163 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((57913/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 481883/5000000) (δ := 6669/500000000) (ψ := -29637/125000) 264 214
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t163 : ((18143395477/250000000000 : ℚ) : ℝ) ≤ stT264 163 := by
  have hc : ((463279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18143395477/250000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((463279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c164 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-416313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2500229/5000000) (δ := 6669/500000000) (ψ := -29637/125000) 264 214
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t164 : ((-325124959447/10000000000000 : ℚ) : ℝ) ≤ stT264 164 := by
  have hc : ((-416363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325124959447/10000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-416363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c165 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-894517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3347683/5000000) (δ := 6679/500000000) (ψ := -29637/125000) 264 215
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t165 : ((-696419514933/10000000000000 : ℚ) : ℝ) ≤ stT264 165 := by
  have hc : ((-894567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-696419514933/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-894567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c166 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((468699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338431/1250000) (δ := 6679/500000000) (ψ := -29637/125000) 264 215
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t166 : ((7274838427/200000000000 : ℚ) : ℝ) ≤ stT264 166 := by
  have hc : ((468649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7274838427/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((468649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c167 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((438159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 628289/5000000) (δ := 6679/500000000) (ψ := -29637/125000) 264 215
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t167 : ((169519083141/2500000000000 : ℚ) : ℝ) ≤ stT264 167 := by
  have hc : ((219067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169519083141/2500000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((219067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c168 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-486379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1299211/2500000) (δ := 6679/500000000) (ψ := -29637/125000) 264 215
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t168 : ((-375288242793/10000000000000 : ℚ) : ℝ) ≤ stT264 168 := by
  have hc : ((-486429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375288242793/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-486429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c169 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-875691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6594151/10000000) (δ := 13251/1000000000) (ψ := -29637/125000) 264 216
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t169 : ((-673647125171/10000000000000 : ℚ) : ℝ) ≤ stT264 169 := by
  have hc : ((-875741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-673647125171/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-875741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c170 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((94241/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2700349/10000000) (δ := 13251/1000000000) (ψ := -29637/125000) 264 216
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t170 : ((18067946171/500000000000 : ℚ) : ℝ) ≤ stT264 170 := by
  have hc : ((94231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18067946171/500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((94231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c171 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((892361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1170617/10000000) (δ := 13251/1000000000) (ψ := -29637/125000) 264 216
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t171 : ((682367175609/10000000000000 : ℚ) : ℝ) ≤ stT264 171 := by
  have hc : ((892311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((682367175609/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((892311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c172 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-423049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5019011/10000000) (δ := 13251/1000000000) (ψ := -29637/125000) 264 216
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t172 : ((-322610025807/10000000000000 : ℚ) : ℝ) ≤ stT264 172 := by
  have hc : ((-423099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-322610025807/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-423099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c173 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-922439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3431433/5000000) (δ := 13259/1000000000) (ψ := -29637/125000) 264 217
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t173 : ((-350677735927/5000000000000 : ℚ) : ℝ) ≤ stT264 173 := by
  have hc : ((-922489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-350677735927/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-922489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c174 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((340329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -382353/1250000) (δ := 13259/1000000000) (ψ := -29637/125000) 264 217
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t174 : ((128982414671/5000000000000 : ℚ) : ℝ) ≤ stT264 174 := by
  have hc : ((340279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128982414671/5000000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((340279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c175 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((479211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 361719/5000000) (δ := 13259/1000000000) (ψ := -29637/125000) 264 217
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t175 : ((22639382163/312500000000 : ℚ) : ℝ) ≤ stT264 175 := by
  have hc : ((239593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22639382163/312500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((239593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c176 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-221011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2242059/5000000) (δ := 13259/1000000000) (ψ := -29637/125000) 264 217
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t176 : ((-166631139519/10000000000000 : ℚ) : ℝ) ≤ stT264 176 := by
  have hc : ((-221061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166631139519/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-221061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c177 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-494547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7484417/10000000) (δ := 13367/1000000000) (ψ := -29637/125000) 264 218
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t177 : ((-92935890021/1250000000000 : ℚ) : ℝ) ≤ stT264 177 := by
  have hc : ((-123643/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92935890021/1250000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-123643/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c178 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((16077/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3766109/10000000) (δ := 13367/1000000000) (ψ := -29637/125000) 264 218
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t178 : ((24081681499/5000000000000 : ℚ) : ℝ) ≤ stT264 178 := by
  have hc : ((32129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24081681499/5000000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((32129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c179 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((124953/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68591/10000000) (δ := 13367/1000000000) (ψ := -29637/125000) 264 218
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t179 : ((74711659269/1000000000000 : ℚ) : ℝ) ≤ stT264 179 := by
  have hc : ((499787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c179).1
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

theorem st264_c180 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((15893/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3608269/10000000) (δ := 13367/1000000000) (ψ := -29637/125000) 264 218
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t180 : ((9473014837/1000000000000 : ℚ) : ℝ) ≤ stT264 180 := by
  have hc : ((63547/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9473014837/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((63547/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c181 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-486179/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7264801/10000000) (δ := 13367/1000000000) (ψ := -29637/125000) 264 218
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t181 : ((-18069650109/250000000000 : ℚ) : ℝ) ≤ stT264 181 := by
  have hc : ((-121551/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18069650109/250000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-121551/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c182 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-172357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4806827/10000000) (δ := 13329/1000000000) (ψ := -29637/125000) 264 219
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t182 : ((-51111263/2000000000 : ℚ) : ℝ) ≤ stT264 182 := by
  have hc : ((-86191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51111263/2000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-86191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c183 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((888769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1190357/10000000) (δ := 13329/1000000000) (ψ := -29637/125000) 264 219
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t183 : ((656959747899/10000000000000 : ℚ) : ℝ) ≤ stT264 183 := by
  have hc : ((888719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((656959747899/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((888719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c184 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((142857/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2406379/10000000) (δ := 13329/1000000000) (ψ := -29637/125000) 264 219
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t184 : ((210612502001/5000000000000 : ℚ) : ℝ) ≤ stT264 184 := by
  have hc : ((285689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210612502001/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((285689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c185 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-732959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1196729/2000000) (δ := 13329/1000000000) (ψ := -29637/125000) 264 219
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t185 : ((-107783842387/2000000000000 : ℚ) : ℝ) ≤ stT264 185 := by
  have hc : ((-733009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107783842387/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-733009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c186 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-195171/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -616639/1000000) (δ := 6611/500000000) (ψ := -29637/125000) 264 220
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t186 : ((-71557784403/1250000000000 : ℚ) : ℝ) ≤ stT264 186 := by
  have hc : ((-390367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71557784403/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-390367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c187 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((248357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262747/1000000) (δ := 6611/500000000) (ψ := -29637/125000) 264 220
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t187 : ((5674944947/156250000000 : ℚ) : ℝ) ≤ stT264 187 := by
  have hc : ((62083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5674944947/156250000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((62083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c188 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((234237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223127/2500000) (δ := 6611/500000000) (ψ := -29637/125000) 264 220
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t188 : ((85412774619/1250000000000 : ℚ) : ℝ) ≤ stT264 188 := by
  have hc : ((468449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85412774619/1250000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((468449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c189 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-18567/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2196937/5000000) (δ := 6611/500000000) (ψ := -29637/125000) 264 220
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t189 : ((-3377285699/250000000000 : ℚ) : ℝ) ≤ stT264 189 := by
  have hc : ((-4643/25000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3377285699/250000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-4643/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c190 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-999959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7831269/10000000) (δ := 1661/125000000) (ψ := -29637/125000) 264 221
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t190 : ((-725483529293/10000000000000 : ℚ) : ℝ) ≤ stT264 190 := by
  have hc : ((-1000009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-725483529293/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-1000009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c191 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-43741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -873333/2000000) (δ := 1661/125000000) (ψ := -29637/125000) 264 221
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t191 : ((-2532715101/200000000000 : ℚ) : ℝ) ≤ stT264 191 := by
  have hc : ((-87507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2532715101/200000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-87507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c192 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((466509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -920211/10000000) (δ := 1661/125000000) (ψ := -29637/125000) 264 221
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t192 : ((84163859627/1250000000000 : ℚ) : ℝ) ≤ stT264 192 := by
  have hc : ((116621/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((84163859627/1250000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((116621/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c193 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((268743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2508357/10000000) (δ := 1661/125000000) (ψ := -29637/125000) 264 221
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t193 : ((19342724717/500000000000 : ℚ) : ℝ) ≤ stT264 193 := by
  have hc : ((134359/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19342724717/500000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((134359/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c194 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-89399/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5919237/10000000) (δ := 1661/125000000) (ψ := -29637/125000) 264 221
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t194 : ((-256757215539/5000000000000 : ℚ) : ℝ) ≤ stT264 194 := by
  have hc : ((-357621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256757215539/5000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-357621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c195 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-834577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3197701/5000000) (δ := 2679/200000000) (ψ := -29637/125000) 264 222
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t195 : ((-119537782821/2000000000000 : ℚ) : ℝ) ≤ stT264 195 := by
  have hc : ((-834627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119537782821/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-834627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c196 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((355101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -754859/2500000) (δ := 2679/200000000) (ψ := -29637/125000) 264 222
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t196 : ((50721520707/2000000000000 : ℚ) : ℝ) ≤ stT264 196 := by
  have hc : ((355051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50721520707/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((355051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c197 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((2477/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33937/1000000) (δ := 2679/200000000) (ψ := -29637/125000) 264 222
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t197 : ((282351861/4000000000 : ℚ) : ℝ) ≤ stT264 197 := by
  have hc : ((3963/4000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282351861/4000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((3963/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c198 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((98179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 920287/2500000) (δ := 2679/200000000) (ψ := -29637/125000) 264 222
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t198 : ((69737238301/10000000000000 : ℚ) : ℝ) ≤ stT264 198 := by
  have hc : ((98129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69737238301/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((98129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c199 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-235759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 437881/625000) (δ := 2679/200000000) (ψ := -29637/125000) 264 222
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t199 : ((-167134172463/2500000000000 : ℚ) : ℝ) ≤ stT264 199 := by
  have hc : ((-471543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167134172463/2500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-471543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c200 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-22143/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2696809/5000000) (δ := 133/10000000) (ψ := -29637/125000) 264 223
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t200 : ((-3131776903/80000000000 : ℚ) : ℝ) ≤ stT264 200 := by
  have hc : ((-4429/8000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3131776903/80000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-4429/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c201 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((333463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1050901/5000000) (δ := 133/10000000) (ψ := -29637/125000) 264 223
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t201 : ((23518882611/500000000000 : ℚ) : ℝ) ≤ stT264 201 := by
  have hc : ((166719/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23518882611/500000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((166719/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c202 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((35673/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 58679/500000) (δ := 133/10000000) (ψ := -29637/125000) 264 223
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t202 : ((25098008587/400000000000 : ℚ) : ℝ) ≤ stT264 202 := by
  have hc : ((35671/40000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25098008587/400000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((35671/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c203 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-200969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2216429/5000000) (δ := 133/10000000) (ψ := -29637/125000) 264 223
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t203 : ((-141087798397/10000000000000 : ℚ) : ℝ) ≤ stT264 203 := by
  have hc : ((-201019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141087798397/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-201019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c204 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-99747/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3838049/5000000) (δ := 133/10000000) (ψ := -29637/125000) 264 223
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t204 : ((-8730058129/125000000000 : ℚ) : ℝ) ≤ stT264 204 := by
  have hc : ((-12469/12500 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8730058129/125000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-12469/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c205 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-343827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -960893/2000000) (δ := 1321/100000000) (ψ := -29637/125000) 264 224
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t205 : ((-240174356987/10000000000000 : ℚ) : ℝ) ≤ stT264 205 := by
  have hc : ((-343877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240174356987/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-343877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c206 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((803819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592773/10000000) (δ := 1321/100000000) (ψ := -29637/125000) 264 224
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t206 : ((560012386677/10000000000000 : ℚ) : ℝ) ≤ stT264 206 := by
  have hc : ((803769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((560012386677/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((803769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c207 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((50081/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1603343/10000000) (δ := 1321/100000000) (ψ := -29637/125000) 264 224
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t207 : ((34806526863/625000000000 : ℚ) : ℝ) ≤ stT264 207 := by
  have hc : ((400623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34806526863/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((400623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c208 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-336159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4784081/10000000) (δ := 1321/100000000) (ψ := -29637/125000) 264 224
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t208 : ((-1821244153/78125000000 : ℚ) : ℝ) ≤ stT264 208 := by
  have hc : ((-336209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1821244153/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-336209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c209 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-999269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -775839/1000000) (δ := 13317/1000000000) (ψ := -29637/125000) 264 225
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t209 : ((-138248788417/2000000000000 : ℚ) : ℝ) ≤ stT264 209 := by
  have hc : ((-999319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138248788417/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-999319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c210 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-67263/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1152003/2500000) (δ := 13317/1000000000) (ψ := -29637/125000) 264 225
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t210 : ((-46424535183/2500000000000 : ℚ) : ℝ) ≤ stT264 210 := by
  have hc : ((-134551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46424535183/2500000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-134551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c211 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((831471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184077/1250000) (δ := 13317/1000000000) (ψ := -29637/125000) 264 225
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t211 : ((143093374047/2500000000000 : ℚ) : ℝ) ≤ stT264 211 := by
  have hc : ((831421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143093374047/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((831421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c212 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((1581/2000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 164793/1000000) (δ := 13317/1000000000) (ψ := -29637/125000) 264 225
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t212 : ((5428826409/100000000000 : ℚ) : ℝ) ≤ stT264 212 := by
  have hc : ((15809/20000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5428826409/100000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((15809/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c213 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-324737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148557/312500) (δ := 13317/1000000000) (ψ := -29637/125000) 264 225
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t213 : ((-222540479743/10000000000000 : ℚ) : ℝ) ≤ stT264 213 := by
  have hc : ((-324787/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222540479743/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-324787/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c214 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-499997/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3922599/5000000) (δ := 13317/1000000000) (ψ := -29637/125000) 264 225
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t214 : ((-85452009723/1250000000000 : ℚ) : ℝ) ≤ stT264 214 := by
  have hc : ((-250011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85452009723/1250000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-250011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c215 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-42103/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2392923/5000000) (δ := 13379/1000000000) (ψ := -29637/125000) 264 226
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t215 : ((-22974638363/1000000000000 : ℚ) : ℝ) ≤ stT264 215 := by
  have hc : ((-168437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22974638363/1000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-168437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c216 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((771709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -861591/5000000) (δ := 13379/1000000000) (ψ := -29637/125000) 264 226
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t216 : ((525046815167/10000000000000 : ℚ) : ℝ) ≤ stT264 216 := by
  have hc : ((771659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((525046815167/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((771659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c217 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((215687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 331323/2500000) (δ := 13379/1000000000) (ψ := -29637/125000) 264 226
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t217 : ((73204670139/1250000000000 : ℚ) : ℝ) ≤ stT264 217 := by
  have hc : ((431349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73204670139/1250000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((431349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c218 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-689/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2179887/5000000) (δ := 13379/1000000000) (ψ := -29637/125000) 264 226
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t218 : ((-583481889/50000000000 : ℚ) : ℝ) ≤ stT264 218 := by
  have hc : ((-1723/10000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583481889/50000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-1723/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c219 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-982111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1845099/2500000) (δ := 13379/1000000000) (ψ := -29637/125000) 264 226
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t219 : ((-331841754909/5000000000000 : ℚ) : ℝ) ≤ stT264 219 := by
  have hc : ((-982161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-331841754909/5000000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-982161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c220 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-264533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5320739/10000000) (δ := 1659/125000000) (ψ := -29637/125000) 264 227
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t220 : ((-445912509/12500000000 : ℚ) : ℝ) ≤ stT264 220 := by
  have hc : ((-132279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-445912509/12500000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-132279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c221 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((59703/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2327507/10000000) (δ := 1659/125000000) (ψ := -29637/125000) 264 227
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t221 : ((627455829/15625000000 : ℚ) : ℝ) ≤ stT264 221 := by
  have hc : ((29849/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((627455829/15625000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((29849/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c222 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((966171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652129/10000000) (δ := 1659/125000000) (ψ := -29637/125000) 264 227
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t222 : ((162104476469/2500000000000 : ℚ) : ℝ) ≤ stT264 222 := by
  have hc : ((966121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162104476469/2500000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((966121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c223 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((12311/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3618433/10000000) (δ := 1659/125000000) (ψ := -29637/125000) 264 227
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t223 : ((4120350297/500000000000 : ℚ) : ℝ) ≤ stT264 223 := by
  have hc : ((6153/50000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4120350297/500000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((6153/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c224 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-435637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6571471/10000000) (δ := 1659/125000000) (ψ := -29637/125000) 264 227
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t224 : ((-72772326987/1250000000000 : ℚ) : ℝ) ≤ stT264 224 := by
  have hc : ((-217831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72772326987/1250000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-217831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c225 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-49261/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1549147/2500000) (δ := 6619/500000000) (ψ := -29637/125000) 264 228
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t225 : ((-262742131371/5000000000000 : ℚ) : ℝ) ≤ stT264 225 := by
  have hc : ((-394113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262742131371/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-394113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c226 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((51973/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -653957/2000000) (δ := 13219/500000000) (ψ := -29637/125000) 264 228
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t226 : ((3456526797/200000000000 : ℚ) : ℝ) ≤ stT264 226 := by
  have hc : ((51963/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3456526797/200000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((51963/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c227 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((989887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88963/2500000) (δ := 6619/500000000) (ψ := -29637/125000) 264 228
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t227 : ((656977583151/10000000000000 : ℚ) : ℝ) ≤ stT264 227 := by
  have hc : ((989837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((656977583151/10000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((989837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c228 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((262493/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 636311/2500000) (δ := 6619/500000000) (ψ := -29637/125000) 264 228
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t228 : ((21727954061/625000000000 : ℚ) : ℝ) ≤ stT264 228 := by
  have hc : ((65617/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21727954061/625000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((65617/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c229 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-113369/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1358417/2500000) (δ := 6619/500000000) (ψ := -29637/125000) 264 228
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t229 : ((-74922997401/2000000000000 : ℚ) : ℝ) ≤ stT264 229 := by
  have hc : ((-113379/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74922997401/2000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-113379/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c230 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-983447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7398477/10000000) (δ := 6673/500000000) (ψ := -29637/125000) 264 229
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t230 : ((-648499235357/10000000000000 : ℚ) : ℝ) ≤ stT264 230 := by
  have hc : ((-983497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-648499235357/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-983497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c231 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-48173/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4535133/10000000) (δ := 6673/500000000) (ψ := -29637/125000) 264 229
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t231 : ((-990690663/62500000000 : ℚ) : ℝ) ≤ stT264 231 := by
  have hc : ((-48183/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-990690663/62500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-48183/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c232 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((195383/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1684197/10000000) (δ := 6673/500000000) (ψ := -29637/125000) 264 229
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t232 : ((64133492553/1250000000000 : ℚ) : ℝ) ≤ stT264 232 := by
  have hc : ((390741/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64133492553/1250000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((390741/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c233 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((895247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1154529/10000000) (δ := 6673/500000000) (ψ := -29637/125000) 264 229
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t233 : ((586462353837/10000000000000 : ℚ) : ℝ) ≤ stT264 233 := by
  have hc : ((895197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((586462353837/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((895197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c234 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-10823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3981111/10000000) (δ := 6673/500000000) (ψ := -29637/125000) 264 229
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t234 : ((-221611419/156250000000 : ℚ) : ℝ) ≤ stT264 234 := by
  have hc : ((-339/15625 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221611419/156250000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-339/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c235 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-911719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1359123/2000000) (δ := 6673/500000000) (ψ := -29637/125000) 264 229
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t235 : ((-594773360001/10000000000000 : ℚ) : ℝ) ≤ stT264 235 := by
  have hc : ((-911769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-594773360001/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-911769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c236 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-766337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6109791/10000000) (δ := 267/20000000) (ψ := -29637/125000) 264 230
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t236 : ((-99775157143/2000000000000 : ℚ) : ℝ) ≤ stT264 236 := by
  have hc : ((-766387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99775157143/2000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-766387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c237 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((120381/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3319113/10000000) (δ := 267/20000000) (ψ := -29637/125000) 264 230
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t237 : ((19544881641/1250000000000 : ℚ) : ℝ) ≤ stT264 237 := by
  have hc : ((30089/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19544881641/1250000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((30089/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c238 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((976747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -540183/10000000) (δ := 267/20000000) (ψ := -29637/125000) 264 230
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t238 : ((633097925491/10000000000000 : ℚ) : ℝ) ≤ stT264 238 := by
  have hc : ((976697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633097925491/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((976697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c239 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((628749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2227131/10000000) (δ := 267/20000000) (ψ := -29637/125000) 264 230
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t239 : ((203335716677/5000000000000 : ℚ) : ℝ) ≤ stT264 239 := by
  have hc : ((628699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203335716677/5000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((628699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c240 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-102479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 996579/2000000) (δ := 267/20000000) (ψ := -29637/125000) 264 230
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t240 : ((-66158058267/2500000000000 : ℚ) : ℝ) ≤ stT264 240 := by
  have hc : ((-204983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66158058267/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-204983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c241 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-499357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 309087/400000) (δ := 267/20000000) (ψ := -29637/125000) 264 230
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t241 : ((-160840205487/2500000000000 : ℚ) : ℝ) ≤ stT264 241 := by
  have hc : ((-249691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160840205487/2500000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-249691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c242 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-504107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -262393/500000) (δ := 13243/1000000000) (ψ := -29637/125000) 264 231
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t242 : ((-12963388941/400000000000 : ℚ) : ℝ) ≤ stT264 242 := by
  have hc : ((-504157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12963388941/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-504157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c243 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((66431/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1263109/5000000) (δ := 13243/1000000000) (ψ := -29637/125000) 264 231
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t243 : ((340891817/10000000000 : ℚ) : ℝ) ≤ stT264 243 := by
  have hc : ((265699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340891817/10000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((265699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c244 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((199457/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18427/1000000) (δ := 13243/1000000000) (ψ := -29637/125000) 264 231
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t244 : ((15960347281/250000000000 : ℚ) : ℝ) ≤ stT264 244 := by
  have hc : ((199447/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15960347281/250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((199447/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c245 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((101333/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2883637/10000000) (δ := 26443/1000000000) (ψ := -29637/125000) 264 231
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t245 : ((32365617879/1250000000000 : ℚ) : ℝ) ≤ stT264 245 := by
  have hc : ((202641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32365617879/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((202641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c246 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-305777/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 348253/625000) (δ := 13243/1000000000) (ψ := -29637/125000) 264 231
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t246 : ((-97486160877/2500000000000 : ℚ) : ℝ) ≤ stT264 246 := by
  have hc : ((-152901/250000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97486160877/2500000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-152901/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c247 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-987509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7458427/10000000) (δ := 13267/1000000000) (ψ := -29637/125000) 264 232
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t247 : ((-125673795663/2000000000000 : ℚ) : ℝ) ≤ stT264 247 := by
  have hc : ((-987559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125673795663/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-987559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c248 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((-84763/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4791763/10000000) (δ := 13267/1000000000) (ψ := -29637/125000) 264 232
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t248 : ((-107665054551/5000000000000 : ℚ) : ℝ) ≤ stT264 248 := by
  have hc : ((-169551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107665054551/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-169551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c249 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((328357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2135857/10000000) (δ := 13267/1000000000) (ψ := -29637/125000) 264 232
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t249 : ((13004491773/312500000000 : ℚ) : ℝ) ≤ stT264 249 := by
  have hc : ((82083/125000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13004491773/312500000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((82083/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_c250 :
    |Real.cos (((264 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((195861/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 509489/10000000) (δ := 13267/1000000000) (ψ := -29637/125000) 264 232
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st264_t250 : ((24773388841/400000000000 : ℚ) : ℝ) ≤ stT264 250 := by
  have hc : ((195851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((264 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st264_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24773388841/400000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((195851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st264_p1 : ((485987/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT264 (i+1) := by
  rw [Finset.sum_range_one]
  exact st264_t1

theorem st264_p2 : ((6723400210381/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT264 (i+1))
      = (∑ i ∈ Finset.range 1, stT264 (i+1)) + stT264 2 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 1
    simpa using h
  have hprev := st264_p1
  have hstep := st264_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p3 : ((478085555931/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT264 (i+1))
      = (∑ i ∈ Finset.range 2, stT264 (i+1)) + stT264 3 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 2
    simpa using h
  have hprev := st264_p2
  have hstep := st264_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p4 : ((3547859392083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT264 (i+1))
      = (∑ i ∈ Finset.range 3, stT264 (i+1)) + stT264 4 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 3
    simpa using h
  have hprev := st264_p3
  have hstep := st264_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p5 : ((2956678789971/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT264 (i+1))
      = (∑ i ∈ Finset.range 4, stT264 (i+1)) + stT264 5 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 4
    simpa using h
  have hprev := st264_p4
  have hstep := st264_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p6 : ((5021902509579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT264 (i+1))
      = (∑ i ∈ Finset.range 5, stT264 (i+1)) + stT264 6 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 5
    simpa using h
  have hprev := st264_p5
  have hstep := st264_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p7 : ((1118574130159/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT264 (i+1))
      = (∑ i ∈ Finset.range 6, stT264 (i+1)) + stT264 7 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 6
    simpa using h
  have hprev := st264_p6
  have hstep := st264_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p8 : ((4103590592907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT264 (i+1))
      = (∑ i ∈ Finset.range 7, stT264 (i+1)) + stT264 8 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 7
    simpa using h
  have hprev := st264_p7
  have hstep := st264_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p9 : ((381853589561/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT264 (i+1))
      = (∑ i ∈ Finset.range 8, stT264 (i+1)) + stT264 9 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 8
    simpa using h
  have hprev := st264_p8
  have hstep := st264_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p10 : ((1360766198637/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT264 (i+1))
      = (∑ i ∈ Finset.range 9, stT264 (i+1)) + stT264 10 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 9
    simpa using h
  have hprev := st264_p9
  have hstep := st264_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p11 : ((1510231380273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT264 (i+1))
      = (∑ i ∈ Finset.range 10, stT264 (i+1)) + stT264 11 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 10
    simpa using h
  have hprev := st264_p10
  have hstep := st264_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p12 : ((4829911053781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT264 (i+1))
      = (∑ i ∈ Finset.range 11, stT264 (i+1)) + stT264 12 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 11
    simpa using h
  have hprev := st264_p11
  have hstep := st264_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p13 : ((5834026220281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT264 (i+1))
      = (∑ i ∈ Finset.range 12, stT264 (i+1)) + stT264 13 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 12
    simpa using h
  have hprev := st264_p12
  have hstep := st264_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p14 : ((8197871355921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT264 (i+1))
      = (∑ i ∈ Finset.range 13, stT264 (i+1)) + stT264 14 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 13
    simpa using h
  have hprev := st264_p13
  have hstep := st264_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p15 : ((9320894126581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT264 (i+1))
      = (∑ i ∈ Finset.range 14, stT264 (i+1)) + stT264 15 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 14
    simpa using h
  have hprev := st264_p14
  have hstep := st264_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p16 : ((6875398148383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT264 (i+1))
      = (∑ i ∈ Finset.range 15, stT264 (i+1)) + stT264 16 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 15
    simpa using h
  have hprev := st264_p15
  have hstep := st264_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p17 : ((8996277381499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT264 (i+1))
      = (∑ i ∈ Finset.range 16, stT264 (i+1)) + stT264 17 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 16
    simpa using h
  have hprev := st264_p16
  have hstep := st264_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p18 : ((1663461677723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT264 (i+1))
      = (∑ i ∈ Finset.range 17, stT264 (i+1)) + stT264 18 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 17
    simpa using h
  have hprev := st264_p17
  have hstep := st264_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p19 : ((6710615625857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT264 (i+1))
      = (∑ i ∈ Finset.range 18, stT264 (i+1)) + stT264 19 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 18
    simpa using h
  have hprev := st264_p18
  have hstep := st264_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p20 : ((1718383435981/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT264 (i+1))
      = (∑ i ∈ Finset.range 19, stT264 (i+1)) + stT264 20 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 19
    simpa using h
  have hprev := st264_p19
  have hstep := st264_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p21 : ((10702484826657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT264 (i+1))
      = (∑ i ∈ Finset.range 20, stT264 (i+1)) + stT264 21 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 20
    simpa using h
  have hprev := st264_p20
  have hstep := st264_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p22 : ((12529056239823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT264 (i+1))
      = (∑ i ∈ Finset.range 21, stT264 (i+1)) + stT264 22 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 21
    simpa using h
  have hprev := st264_p21
  have hstep := st264_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p23 : ((12938941336479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT264 (i+1))
      = (∑ i ∈ Finset.range 22, stT264 (i+1)) + stT264 23 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 22
    simpa using h
  have hprev := st264_p22
  have hstep := st264_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p24 : ((11090351756439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT264 (i+1))
      = (∑ i ∈ Finset.range 23, stT264 (i+1)) + stT264 24 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 23
    simpa using h
  have hprev := st264_p23
  have hstep := st264_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p25 : ((133184419233/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT264 (i+1))
      = (∑ i ∈ Finset.range 24, stT264 (i+1)) + stT264 25 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 24
    simpa using h
  have hprev := st264_p24
  have hstep := st264_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p26 : ((12443926602423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT264 (i+1))
      = (∑ i ∈ Finset.range 25, stT264 (i+1)) + stT264 26 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 25
    simpa using h
  have hprev := st264_p25
  have hstep := st264_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p27 : ((10532454474193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT264 (i+1))
      = (∑ i ∈ Finset.range 26, stT264 (i+1)) + stT264 27 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 26
    simpa using h
  have hprev := st264_p26
  have hstep := st264_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p28 : ((12341556507107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT264 (i+1))
      = (∑ i ∈ Finset.range 27, stT264 (i+1)) + stT264 28 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 27
    simpa using h
  have hprev := st264_p27
  have hstep := st264_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p29 : ((10500782147309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT264 (i+1))
      = (∑ i ∈ Finset.range 28, stT264 (i+1)) + stT264 29 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 28
    simpa using h
  have hprev := st264_p28
  have hstep := st264_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p30 : ((12220509670403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT264 (i+1))
      = (∑ i ∈ Finset.range 29, stT264 (i+1)) + stT264 30 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 29
    simpa using h
  have hprev := st264_p29
  have hstep := st264_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p31 : ((11422664766469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT264 (i+1))
      = (∑ i ∈ Finset.range 30, stT264 (i+1)) + stT264 31 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 30
    simpa using h
  have hprev := st264_p30
  have hstep := st264_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p32 : ((10449554994911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT264 (i+1))
      = (∑ i ∈ Finset.range 31, stT264 (i+1)) + stT264 32 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 31
    simpa using h
  have hprev := st264_p31
  have hstep := st264_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p33 : ((12105586537679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT264 (i+1))
      = (∑ i ∈ Finset.range 32, stT264 (i+1)) + stT264 33 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 32
    simpa using h
  have hprev := st264_p32
  have hstep := st264_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p34 : ((12589229457529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT264 (i+1))
      = (∑ i ∈ Finset.range 33, stT264 (i+1)) + stT264 34 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 33
    simpa using h
  have hprev := st264_p33
  have hstep := st264_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p35 : ((5547762684123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT264 (i+1))
      = (∑ i ∈ Finset.range 34, stT264 (i+1)) + stT264 35 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 34
    simpa using h
  have hprev := st264_p34
  have hstep := st264_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p36 : ((2446418776569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT264 (i+1))
      = (∑ i ∈ Finset.range 35, stT264 (i+1)) + stT264 36 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 35
    simpa using h
  have hprev := st264_p35
  have hstep := st264_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p37 : ((4930647656149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT264 (i+1))
      = (∑ i ∈ Finset.range 36, stT264 (i+1)) + stT264 37 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 36
    simpa using h
  have hprev := st264_p36
  have hstep := st264_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p38 : ((5514312142279/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT264 (i+1))
      = (∑ i ∈ Finset.range 37, stT264 (i+1)) + stT264 38 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 37
    simpa using h
  have hprev := st264_p37
  have hstep := st264_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p39 : ((12600042995189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT264 (i+1))
      = (∑ i ∈ Finset.range 38, stT264 (i+1)) + stT264 39 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 38
    simpa using h
  have hprev := st264_p38
  have hstep := st264_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p40 : ((14147169135671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT264 (i+1))
      = (∑ i ∈ Finset.range 39, stT264 (i+1)) + stT264 40 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 39
    simpa using h
  have hprev := st264_p39
  have hstep := st264_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p41 : ((15557933019881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT264 (i+1))
      = (∑ i ∈ Finset.range 40, stT264 (i+1)) + stT264 41 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 40
    simpa using h
  have hprev := st264_p40
  have hstep := st264_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p42 : ((3379110876171/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT264 (i+1))
      = (∑ i ∈ Finset.range 41, stT264 (i+1)) + stT264 42 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 41
    simpa using h
  have hprev := st264_p41
  have hstep := st264_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p43 : ((1826821015419/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT264 (i+1))
      = (∑ i ∈ Finset.range 42, stT264 (i+1)) + stT264 43 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 42
    simpa using h
  have hprev := st264_p42
  have hstep := st264_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p44 : ((9866827796221/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT264 (i+1))
      = (∑ i ∈ Finset.range 43, stT264 (i+1)) + stT264 44 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 43
    simpa using h
  have hprev := st264_p43
  have hstep := st264_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p45 : ((21214672498809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT264 (i+1))
      = (∑ i ∈ Finset.range 44, stT264 (i+1)) + stT264 45 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 44
    simpa using h
  have hprev := st264_p44
  have hstep := st264_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p46 : ((22436113635627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT264 (i+1))
      = (∑ i ∈ Finset.range 45, stT264 (i+1)) + stT264 46 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 45
    simpa using h
  have hprev := st264_p45
  have hstep := st264_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p47 : ((22964669687267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT264 (i+1))
      = (∑ i ∈ Finset.range 46, stT264 (i+1)) + stT264 47 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 46
    simpa using h
  have hprev := st264_p46
  have hstep := st264_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p48 : ((22463927911843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT264 (i+1))
      = (∑ i ∈ Finset.range 47, stT264 (i+1)) + stT264 48 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 47
    simpa using h
  have hprev := st264_p47
  have hstep := st264_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p49 : ((21135525951911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT264 (i+1))
      = (∑ i ∈ Finset.range 48, stT264 (i+1)) + stT264 49 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 48
    simpa using h
  have hprev := st264_p48
  have hstep := st264_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p50 : ((19946969594607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT264 (i+1))
      = (∑ i ∈ Finset.range 49, stT264 (i+1)) + stT264 50 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 49
    simpa using h
  have hprev := st264_p49
  have hstep := st264_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p51 : ((20027097817047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT264 (i+1))
      = (∑ i ∈ Finset.range 50, stT264 (i+1)) + stT264 51 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 50
    simpa using h
  have hprev := st264_p50
  have hstep := st264_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p52 : ((21326495047797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT264 (i+1))
      = (∑ i ∈ Finset.range 51, stT264 (i+1)) + stT264 52 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 51
    simpa using h
  have hprev := st264_p51
  have hstep := st264_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p53 : ((11091332208951/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT264 (i+1))
      = (∑ i ∈ Finset.range 52, stT264 (i+1)) + stT264 53 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 52
    simpa using h
  have hprev := st264_p52
  have hstep := st264_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p54 : ((2133174003033/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT264 (i+1))
      = (∑ i ∈ Finset.range 53, stT264 (i+1)) + stT264 54 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 53
    simpa using h
  have hprev := st264_p53
  have hstep := st264_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p55 : ((2017769436113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT264 (i+1))
      = (∑ i ∈ Finset.range 54, stT264 (i+1)) + stT264 55 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 54
    simpa using h
  have hprev := st264_p54
  have hstep := st264_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p56 : ((5204331645543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT264 (i+1))
      = (∑ i ∈ Finset.range 55, stT264 (i+1)) + stT264 56 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 55
    simpa using h
  have hprev := st264_p55
  have hstep := st264_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p57 : ((5488521906931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT264 (i+1))
      = (∑ i ∈ Finset.range 56, stT264 (i+1)) + stT264 57 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 56
    simpa using h
  have hprev := st264_p56
  have hstep := st264_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p58 : ((21149135451579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT264 (i+1))
      = (∑ i ∈ Finset.range 57, stT264 (i+1)) + stT264 58 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 57
    simpa using h
  have hprev := st264_p57
  have hstep := st264_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p59 : ((20298975243779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT264 (i+1))
      = (∑ i ∈ Finset.range 58, stT264 (i+1)) + stT264 59 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 58
    simpa using h
  have hprev := st264_p58
  have hstep := st264_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p60 : ((21469028925859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT264 (i+1))
      = (∑ i ∈ Finset.range 59, stT264 (i+1)) + stT264 60 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 59
    simpa using h
  have hprev := st264_p59
  have hstep := st264_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p61 : ((21580893397651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT264 (i+1))
      = (∑ i ∈ Finset.range 60, stT264 (i+1)) + stT264 61 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 60
    simpa using h
  have hprev := st264_p60
  have hstep := st264_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p62 : ((20380215726823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT264 (i+1))
      = (∑ i ∈ Finset.range 61, stT264 (i+1)) + stT264 62 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 61
    simpa using h
  have hprev := st264_p61
  have hstep := st264_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p63 : ((21301627176411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT264 (i+1))
      = (∑ i ∈ Finset.range 62, stT264 (i+1)) + stT264 63 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 62
    simpa using h
  have hprev := st264_p62
  have hstep := st264_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p64 : ((21544494676411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT264 (i+1))
      = (∑ i ∈ Finset.range 63, stT264 (i+1)) + stT264 64 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 63
    simpa using h
  have hprev := st264_p63
  have hstep := st264_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p65 : ((4082751990043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT264 (i+1))
      = (∑ i ∈ Finset.range 64, stT264 (i+1)) + stT264 65 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 64
    simpa using h
  have hprev := st264_p64
  have hstep := st264_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p66 : ((21513730549809/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT264 (i+1))
      = (∑ i ∈ Finset.range 65, stT264 (i+1)) + stT264 66 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 65
    simpa using h
  have hprev := st264_p65
  have hstep := st264_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p67 : ((1323719694609/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT264 (i+1))
      = (∑ i ∈ Finset.range 66, stT264 (i+1)) + stT264 67 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 66
    simpa using h
  have hprev := st264_p66
  have hstep := st264_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p68 : ((4121202749677/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT264 (i+1))
      = (∑ i ∈ Finset.range 67, stT264 (i+1)) + stT264 68 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 67
    simpa using h
  have hprev := st264_p67
  have hstep := st264_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p69 : ((21730178756501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT264 (i+1))
      = (∑ i ∈ Finset.range 68, stT264 (i+1)) + stT264 69 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 68
    simpa using h
  have hprev := st264_p68
  have hstep := st264_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p70 : ((10292615922651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT264 (i+1))
      = (∑ i ∈ Finset.range 69, stT264 (i+1)) + stT264 70 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 69
    simpa using h
  have hprev := st264_p69
  have hstep := st264_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p71 : ((10664038025097/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT264 (i+1))
      = (∑ i ∈ Finset.range 70, stT264 (i+1)) + stT264 71 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 70
    simpa using h
  have hprev := st264_p70
  have hstep := st264_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p72 : ((10590193052433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT264 (i+1))
      = (∑ i ∈ Finset.range 71, stT264 (i+1)) + stT264 72 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 71
    simpa using h
  have hprev := st264_p71
  have hstep := st264_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p73 : ((10376232960743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT264 (i+1))
      = (∑ i ∈ Finset.range 72, stT264 (i+1)) + stT264 73 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 72
    simpa using h
  have hprev := st264_p72
  have hstep := st264_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p74 : ((10802963369393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT264 (i+1))
      = (∑ i ∈ Finset.range 73, stT264 (i+1)) + stT264 74 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 73
    simpa using h
  have hprev := st264_p73
  have hstep := st264_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p75 : ((20518883134479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT264 (i+1))
      = (∑ i ∈ Finset.range 74, stT264 (i+1)) + stT264 75 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 74
    simpa using h
  have hprev := st264_p74
  have hstep := st264_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p76 : ((21665834955899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT264 (i+1))
      = (∑ i ∈ Finset.range 75, stT264 (i+1)) + stT264 76 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 75
    simpa using h
  have hprev := st264_p75
  have hstep := st264_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p77 : ((823366934503/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT264 (i+1))
      = (∑ i ∈ Finset.range 76, stT264 (i+1)) + stT264 77 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 76
    simpa using h
  have hprev := st264_p76
  have hstep := st264_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p78 : ((67274716431/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT264 (i+1))
      = (∑ i ∈ Finset.range 77, stT264 (i+1)) + stT264 78 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 77
    simpa using h
  have hprev := st264_p77
  have hstep := st264_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p79 : ((129684517191/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT264 (i+1))
      = (∑ i ∈ Finset.range 78, stT264 (i+1)) + stT264 79 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 78
    simpa using h
  have hprev := st264_p78
  have hstep := st264_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p80 : ((2136662106491/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT264 (i+1))
      = (∑ i ∈ Finset.range 79, stT264 (i+1)) + stT264 80 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 79
    simpa using h
  have hprev := st264_p79
  have hstep := st264_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p81 : ((2088645956967/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT264 (i+1))
      = (∑ i ∈ Finset.range 80, stT264 (i+1)) + stT264 81 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 80
    simpa using h
  have hprev := st264_p80
  have hstep := st264_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p82 : ((4252827722523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT264 (i+1))
      = (∑ i ∈ Finset.range 81, stT264 (i+1)) + stT264 82 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 81
    simpa using h
  have hprev := st264_p81
  have hstep := st264_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p83 : ((10474766636799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT264 (i+1))
      = (∑ i ∈ Finset.range 82, stT264 (i+1)) + stT264 83 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 82
    simpa using h
  have hprev := st264_p82
  have hstep := st264_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p84 : ((2655133213483/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT264 (i+1))
      = (∑ i ∈ Finset.range 83, stT264 (i+1)) + stT264 84 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 83
    simpa using h
  have hprev := st264_p83
  have hstep := st264_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p85 : ((10466554429399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT264 (i+1))
      = (∑ i ∈ Finset.range 84, stT264 (i+1)) + stT264 85 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 84
    simpa using h
  have hprev := st264_p84
  have hstep := st264_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p86 : ((21294368892011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT264 (i+1))
      = (∑ i ∈ Finset.range 85, stT264 (i+1)) + stT264 86 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 85
    simpa using h
  have hprev := st264_p85
  have hstep := st264_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p87 : ((20846219225333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT264 (i+1))
      = (∑ i ∈ Finset.range 86, stT264 (i+1)) + stT264 87 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 86
    simpa using h
  have hprev := st264_p86
  have hstep := st264_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p88 : ((10704220466783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT264 (i+1))
      = (∑ i ∈ Finset.range 87, stT264 (i+1)) + stT264 88 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 87
    simpa using h
  have hprev := st264_p87
  have hstep := st264_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p89 : ((10357063701797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT264 (i+1))
      = (∑ i ∈ Finset.range 88, stT264 (i+1)) + stT264 89 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 88
    simpa using h
  have hprev := st264_p88
  have hstep := st264_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p90 : ((2154367461757/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT264 (i+1))
      = (∑ i ∈ Finset.range 89, stT264 (i+1)) + stT264 90 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 89
    simpa using h
  have hprev := st264_p89
  have hstep := st264_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p91 : ((2059535826831/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT264 (i+1))
      = (∑ i ∈ Finset.range 90, stT264 (i+1)) + stT264 91 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 90
    simpa using h
  have hprev := st264_p90
  have hstep := st264_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p92 : ((10810133506743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT264 (i+1))
      = (∑ i ∈ Finset.range 91, stT264 (i+1)) + stT264 92 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 91
    simpa using h
  have hprev := st264_p91
  have hstep := st264_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p93 : ((10294403355639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT264 (i+1))
      = (∑ i ∈ Finset.range 92, stT264 (i+1)) + stT264 93 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 92
    simpa using h
  have hprev := st264_p92
  have hstep := st264_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p94 : ((21529909268571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT264 (i+1))
      = (∑ i ∈ Finset.range 93, stT264 (i+1)) + stT264 94 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 93
    simpa using h
  have hprev := st264_p93
  have hstep := st264_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p95 : ((2599108694061/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT264 (i+1))
      = (∑ i ∈ Finset.range 94, stT264 (i+1)) + stT264 95 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 94
    simpa using h
  have hprev := st264_p94
  have hstep := st264_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p96 : ((5303230255697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT264 (i+1))
      = (∑ i ∈ Finset.range 95, stT264 (i+1)) + stT264 96 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 95
    simpa using h
  have hprev := st264_p95
  have hstep := st264_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p97 : ((21194176701821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT264 (i+1))
      = (∑ i ∈ Finset.range 96, stT264 (i+1)) + stT264 97 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 96
    simpa using h
  have hprev := st264_p96
  have hstep := st264_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p98 : ((20786412280923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT264 (i+1))
      = (∑ i ∈ Finset.range 97, stT264 (i+1)) + stT264 98 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 97
    simpa using h
  have hprev := st264_p97
  have hstep := st264_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p99 : ((21558946031417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT264 (i+1))
      = (∑ i ∈ Finset.range 98, stT264 (i+1)) + stT264 99 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 98
    simpa using h
  have hprev := st264_p98
  have hstep := st264_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p100 : ((20579969031417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT264 (i+1))
      = (∑ i ∈ Finset.range 99, stT264 (i+1)) + stT264 100 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 99
    simpa using h
  have hprev := st264_p99
  have hstep := st264_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p101 : ((21527821376877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT264 (i+1))
      = (∑ i ∈ Finset.range 100, stT264 (i+1)) + stT264 101 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 100
    simpa using h
  have hprev := st264_p100
  have hstep := st264_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p102 : ((20874003879073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT264 (i+1))
      = (∑ i ∈ Finset.range 101, stT264 (i+1)) + stT264 102 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 101
    simpa using h
  have hprev := st264_p101
  have hstep := st264_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p103 : ((4205252959757/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT264 (i+1))
      = (∑ i ∈ Finset.range 102, stT264 (i+1)) + stT264 103 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 102
    simpa using h
  have hprev := st264_p102
  have hstep := st264_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p104 : ((4288004105957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT264 (i+1))
      = (∑ i ∈ Finset.range 103, stT264 (i+1)) + stT264 104 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 103
    simpa using h
  have hprev := st264_p103
  have hstep := st264_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p105 : ((10296508754883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT264 (i+1))
      = (∑ i ∈ Finset.range 104, stT264 (i+1)) + stT264 105 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 104
    simpa using h
  have hprev := st264_p104
  have hstep := st264_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p106 : ((10778674054583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT264 (i+1))
      = (∑ i ∈ Finset.range 105, stT264 (i+1)) + stT264 106 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 105
    simpa using h
  have hprev := st264_p105
  have hstep := st264_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p107 : ((20871395037131/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT264 (i+1))
      = (∑ i ∈ Finset.range 106, stT264 (i+1)) + stT264 107 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 106
    simpa using h
  have hprev := st264_p106
  have hstep := st264_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p108 : ((20970319148381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT264 (i+1))
      = (∑ i ∈ Finset.range 107, stT264 (i+1)) + stT264 108 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 107
    simpa using h
  have hprev := st264_p107
  have hstep := st264_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p109 : ((860613613643/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT264 (i+1))
      = (∑ i ∈ Finset.range 108, stT264 (i+1)) + stT264 109 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 108
    simpa using h
  have hprev := st264_p108
  have hstep := st264_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p110 : ((5146998411527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT264 (i+1))
      = (∑ i ∈ Finset.range 109, stT264 (i+1)) + stT264 110 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 109
    simpa using h
  have hprev := st264_p109
  have hstep := st264_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p111 : ((21412768367043/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT264 (i+1))
      = (∑ i ∈ Finset.range 110, stT264 (i+1)) + stT264 111 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 110
    simpa using h
  have hprev := st264_p110
  have hstep := st264_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p112 : ((21152220221987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT264 (i+1))
      = (∑ i ∈ Finset.range 111, stT264 (i+1)) + stT264 112 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 111
    simpa using h
  have hprev := st264_p111
  have hstep := st264_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p113 : ((2586043954701/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT264 (i+1))
      = (∑ i ∈ Finset.range 112, stT264 (i+1)) + stT264 113 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 112
    simpa using h
  have hprev := st264_p112
  have hstep := st264_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p114 : ((5399532893727/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT264 (i+1))
      = (∑ i ∈ Finset.range 113, stT264 (i+1)) + stT264 114 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 113
    simpa using h
  have hprev := st264_p113
  have hstep := st264_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p115 : ((10413252101259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT264 (i+1))
      = (∑ i ∈ Finset.range 114, stT264 (i+1)) + stT264 115 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 114
    simpa using h
  have hprev := st264_p114
  have hstep := st264_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p116 : ((2093634477027/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT264 (i+1))
      = (∑ i ∈ Finset.range 115, stT264 (i+1)) + stT264 116 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 115
    simpa using h
  have hprev := st264_p115
  have hstep := st264_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p117 : ((2157108520677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT264 (i+1))
      = (∑ i ∈ Finset.range 116, stT264 (i+1)) + stT264 117 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 116
    simpa using h
  have hprev := st264_p116
  have hstep := st264_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p118 : ((4130693602849/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT264 (i+1))
      = (∑ i ∈ Finset.range 117, stT264 (i+1)) + stT264 118 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 117
    simpa using h
  have hprev := st264_p117
  have hstep := st264_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p119 : ((21152905252001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT264 (i+1))
      = (∑ i ∈ Finset.range 118, stT264 (i+1)) + stT264 119 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 118
    simpa using h
  have hprev := st264_p118
  have hstep := st264_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p120 : ((21471127169651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT264 (i+1))
      = (∑ i ∈ Finset.range 119, stT264 (i+1)) + stT264 120 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 119
    simpa using h
  have hprev := st264_p119
  have hstep := st264_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p121 : ((20593477990977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT264 (i+1))
      = (∑ i ∈ Finset.range 120, stT264 (i+1)) + stT264 121 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 120
    simpa using h
  have hprev := st264_p120
  have hstep := st264_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p122 : ((10641546472331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT264 (i+1))
      = (∑ i ∈ Finset.range 121, stT264 (i+1)) + stT264 122 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 121
    simpa using h
  have hprev := st264_p121
  have hstep := st264_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p123 : ((21391404129949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT264 (i+1))
      = (∑ i ∈ Finset.range 122, stT264 (i+1)) + stT264 123 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 122
    simpa using h
  have hprev := st264_p122
  have hstep := st264_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p124 : ((2058133258841/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT264 (i+1))
      = (∑ i ∈ Finset.range 123, stT264 (i+1)) + stT264 124 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 123
    simpa using h
  have hprev := st264_p123
  have hstep := st264_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p125 : ((1066601705689/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT264 (i+1))
      = (∑ i ∈ Finset.range 124, stT264 (i+1)) + stT264 125 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 124
    simpa using h
  have hprev := st264_p124
  have hstep := st264_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p126 : ((1068464514859/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT264 (i+1))
      = (∑ i ∈ Finset.range 125, stT264 (i+1)) + stT264 126 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 125
    simpa using h
  have hprev := st264_p125
  have hstep := st264_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p127 : ((10289914148067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT264 (i+1))
      = (∑ i ∈ Finset.range 126, stT264 (i+1)) + stT264 127 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 126
    simpa using h
  have hprev := st264_p126
  have hstep := st264_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p128 : ((21310917093573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT264 (i+1))
      = (∑ i ∈ Finset.range 127, stT264 (i+1)) + stT264 128 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 127
    simpa using h
  have hprev := st264_p127
  have hstep := st264_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p129 : ((21410166700273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT264 (i+1))
      = (∑ i ∈ Finset.range 128, stT264 (i+1)) + stT264 129 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 128
    simpa using h
  have hprev := st264_p128
  have hstep := st264_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p130 : ((20587688835961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT264 (i+1))
      = (∑ i ∈ Finset.range 129, stT264 (i+1)) + stT264 130 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 129
    simpa using h
  have hprev := st264_p129
  have hstep := st264_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p131 : ((21218650779937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT264 (i+1))
      = (∑ i ∈ Finset.range 130, stT264 (i+1)) + stT264 131 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 130
    simpa using h
  have hprev := st264_p130
  have hstep := st264_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p132 : ((21498156737601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT264 (i+1))
      = (∑ i ∈ Finset.range 131, stT264 (i+1)) + stT264 132 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 131
    simpa using h
  have hprev := st264_p131
  have hstep := st264_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p133 : ((20634888034901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT264 (i+1))
      = (∑ i ∈ Finset.range 132, stT264 (i+1)) + stT264 133 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 132
    simpa using h
  have hprev := st264_p132
  have hstep := st264_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p134 : ((21050086320137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT264 (i+1))
      = (∑ i ∈ Finset.range 133, stT264 (i+1)) + stT264 134 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 133
    simpa using h
  have hprev := st264_p133
  have hstep := st264_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p135 : ((21589439097001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT264 (i+1))
      = (∑ i ∈ Finset.range 134, stT264 (i+1)) + stT264 135 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 134
    simpa using h
  have hprev := st264_p134
  have hstep := st264_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p136 : ((5192537066911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT264 (i+1))
      = (∑ i ∈ Finset.range 135, stT264 (i+1)) + stT264 136 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 135
    simpa using h
  have hprev := st264_p135
  have hstep := st264_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p137 : ((325380074277/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT264 (i+1))
      = (∑ i ∈ Finset.range 136, stT264 (i+1)) + stT264 137 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 136
    simpa using h
  have hprev := st264_p136
  have hstep := st264_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p138 : ((2700508448553/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT264 (i+1))
      = (∑ i ∈ Finset.range 137, stT264 (i+1)) + stT264 138 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 137
    simpa using h
  have hprev := st264_p137
  have hstep := st264_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p139 : ((4205413841841/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT264 (i+1))
      = (∑ i ∈ Finset.range 138, stT264 (i+1)) + stT264 139 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 138
    simpa using h
  have hprev := st264_p138
  have hstep := st264_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p140 : ((4124212701689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT264 (i+1))
      = (∑ i ∈ Finset.range 139, stT264 (i+1)) + stT264 140 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 139
    simpa using h
  have hprev := st264_p139
  have hstep := st264_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p141 : ((21447560605657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT264 (i+1))
      = (∑ i ∈ Finset.range 140, stT264 (i+1)) + stT264 141 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 140
    simpa using h
  have hprev := st264_p140
  have hstep := st264_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p142 : ((21361989217117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT264 (i+1))
      = (∑ i ∈ Finset.range 141, stT264 (i+1)) + stT264 142 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 141
    simpa using h
  have hprev := st264_p141
  have hstep := st264_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p143 : ((5146647187267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT264 (i+1))
      = (∑ i ∈ Finset.range 142, stT264 (i+1)) + stT264 143 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 142
    simpa using h
  have hprev := st264_p142
  have hstep := st264_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p144 : ((1318297825829/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT264 (i+1))
      = (∑ i ∈ Finset.range 143, stT264 (i+1)) + stT264 144 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 143
    simpa using h
  have hprev := st264_p143
  have hstep := st264_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p145 : ((135018850511/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT264 (i+1))
      = (∑ i ∈ Finset.range 144, stT264 (i+1)) + stT264 145 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 144
    simpa using h
  have hprev := st264_p144
  have hstep := st264_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p146 : ((2605830886977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT264 (i+1))
      = (∑ i ∈ Finset.range 145, stT264 (i+1)) + stT264 146 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 145
    simpa using h
  have hprev := st264_p145
  have hstep := st264_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p147 : ((10346703309969/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT264 (i+1))
      = (∑ i ∈ Finset.range 146, stT264 (i+1)) + stT264 147 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 146
    simpa using h
  have hprev := st264_p146
  have hstep := st264_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p148 : ((2689366613169/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT264 (i+1))
      = (∑ i ∈ Finset.range 147, stT264 (i+1)) + stT264 148 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 147
    simpa using h
  have hprev := st264_p147
  have hstep := st264_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p149 : ((2665097172381/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT264 (i+1))
      = (∑ i ∈ Finset.range 148, stT264 (i+1)) + stT264 149 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 148
    simpa using h
  have hprev := st264_p148
  have hstep := st264_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p150 : ((20580037420199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT264 (i+1))
      = (∑ i ∈ Finset.range 149, stT264 (i+1)) + stT264 150 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 149
    simpa using h
  have hprev := st264_p149
  have hstep := st264_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p151 : ((21051293099331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT264 (i+1))
      = (∑ i ∈ Finset.range 150, stT264 (i+1)) + stT264 151 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 150
    simpa using h
  have hprev := st264_p150
  have hstep := st264_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p152 : ((21622456804377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT264 (i+1))
      = (∑ i ∈ Finset.range 151, stT264 (i+1)) + stT264 152 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 151
    simpa using h
  have hprev := st264_p151
  have hstep := st264_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p153 : ((20964893472297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT264 (i+1))
      = (∑ i ∈ Finset.range 152, stT264 (i+1)) + stT264 153 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 152
    simpa using h
  have hprev := st264_p152
  have hstep := st264_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p154 : ((2574818475321/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT264 (i+1))
      = (∑ i ∈ Finset.range 153, stT264 (i+1)) + stT264 154 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 153
    simpa using h
  have hprev := st264_p153
  have hstep := st264_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p155 : ((21357352807963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT264 (i+1))
      = (∑ i ∈ Finset.range 154, stT264 (i+1)) + stT264 155 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 154
    simpa using h
  have hprev := st264_p154
  have hstep := st264_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p156 : ((21521854704283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT264 (i+1))
      = (∑ i ∈ Finset.range 155, stT264 (i+1)) + stT264 156 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 155
    simpa using h
  have hprev := st264_p155
  have hstep := st264_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p157 : ((10363510752491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT264 (i+1))
      = (∑ i ∈ Finset.range 156, stT264 (i+1)) + stT264 157 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 156
    simpa using h
  have hprev := st264_p156
  have hstep := st264_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p158 : ((20738529236987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT264 (i+1))
      = (∑ i ∈ Finset.range 157, stT264 (i+1)) + stT264 158 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 157
    simpa using h
  have hprev := st264_p157
  have hstep := st264_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p159 : ((4305360896773/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT264 (i+1))
      = (∑ i ∈ Finset.range 158, stT264 (i+1)) + stT264 159 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 158
    simpa using h
  have hprev := st264_p158
  have hstep := st264_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p160 : ((4274913516249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT264 (i+1))
      = (∑ i ∈ Finset.range 159, stT264 (i+1)) + stT264 160 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 159
    simpa using h
  have hprev := st264_p159
  have hstep := st264_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p161 : ((4122901090347/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT264 (i+1))
      = (∑ i ∈ Finset.range 160, stT264 (i+1)) + stT264 161 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 160
    simpa using h
  have hprev := st264_p160
  have hstep := st264_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p162 : ((4174060252857/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT264 (i+1))
      = (∑ i ∈ Finset.range 161, stT264 (i+1)) + stT264 162 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 161
    simpa using h
  have hprev := st264_p161
  have hstep := st264_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p163 : ((4319207416673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT264 (i+1))
      = (∑ i ∈ Finset.range 162, stT264 (i+1)) + stT264 163 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 162
    simpa using h
  have hprev := st264_p162
  have hstep := st264_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p164 : ((10635456061959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT264 (i+1))
      = (∑ i ∈ Finset.range 163, stT264 (i+1)) + stT264 164 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 163
    simpa using h
  have hprev := st264_p163
  have hstep := st264_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p165 : ((4114898521797/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT264 (i+1))
      = (∑ i ∈ Finset.range 164, stT264 (i+1)) + stT264 165 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 164
    simpa using h
  have hprev := st264_p164
  have hstep := st264_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p166 : ((4187646906067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT264 (i+1))
      = (∑ i ∈ Finset.range 165, stT264 (i+1)) + stT264 166 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 165
    simpa using h
  have hprev := st264_p165
  have hstep := st264_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p167 : ((21616310862899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT264 (i+1))
      = (∑ i ∈ Finset.range 166, stT264 (i+1)) + stT264 167 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 166
    simpa using h
  have hprev := st264_p166
  have hstep := st264_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p168 : ((10620511310053/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT264 (i+1))
      = (∑ i ∈ Finset.range 167, stT264 (i+1)) + stT264 168 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 167
    simpa using h
  have hprev := st264_p167
  have hstep := st264_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p169 : ((4113475098987/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT264 (i+1))
      = (∑ i ∈ Finset.range 168, stT264 (i+1)) + stT264 169 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 168
    simpa using h
  have hprev := st264_p168
  have hstep := st264_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p170 : ((4185746883671/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT264 (i+1))
      = (∑ i ∈ Finset.range 169, stT264 (i+1)) + stT264 170 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 169
    simpa using h
  have hprev := st264_p169
  have hstep := st264_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p171 : ((5402775398491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT264 (i+1))
      = (∑ i ∈ Finset.range 170, stT264 (i+1)) + stT264 171 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 170
    simpa using h
  have hprev := st264_p170
  have hstep := st264_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p172 : ((21288491568157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT264 (i+1))
      = (∑ i ∈ Finset.range 171, stT264 (i+1)) + stT264 172 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 171
    simpa using h
  have hprev := st264_p171
  have hstep := st264_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p173 : ((20587136096303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT264 (i+1))
      = (∑ i ∈ Finset.range 172, stT264 (i+1)) + stT264 173 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 172
    simpa using h
  have hprev := st264_p172
  have hstep := st264_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p174 : ((4169020185129/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT264 (i+1))
      = (∑ i ∈ Finset.range 173, stT264 (i+1)) + stT264 174 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 173
    simpa using h
  have hprev := st264_p173
  have hstep := st264_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p175 : ((21569561154861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT264 (i+1))
      = (∑ i ∈ Finset.range 174, stT264 (i+1)) + stT264 175 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 174
    simpa using h
  have hprev := st264_p174
  have hstep := st264_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p176 : ((10701465007671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT264 (i+1))
      = (∑ i ∈ Finset.range 175, stT264 (i+1)) + stT264 176 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 175
    simpa using h
  have hprev := st264_p175
  have hstep := st264_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p177 : ((10329721447587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT264 (i+1))
      = (∑ i ∈ Finset.range 176, stT264 (i+1)) + stT264 177 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 176
    simpa using h
  have hprev := st264_p176
  have hstep := st264_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p178 : ((5176901564543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT264 (i+1))
      = (∑ i ∈ Finset.range 177, stT264 (i+1)) + stT264 178 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 177
    simpa using h
  have hprev := st264_p177
  have hstep := st264_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p179 : ((10727361425431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT264 (i+1))
      = (∑ i ∈ Finset.range 178, stT264 (i+1)) + stT264 179 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 178
    simpa using h
  have hprev := st264_p178
  have hstep := st264_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p180 : ((336710203113/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT264 (i+1))
      = (∑ i ∈ Finset.range 179, stT264 (i+1)) + stT264 180 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 179
    simpa using h
  have hprev := st264_p179
  have hstep := st264_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p181 : ((2603333374359/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT264 (i+1))
      = (∑ i ∈ Finset.range 180, stT264 (i+1)) + stT264 181 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 180
    simpa using h
  have hprev := st264_p180
  have hstep := st264_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p182 : ((321423604373/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT264 (i+1))
      = (∑ i ∈ Finset.range 181, stT264 (i+1)) + stT264 182 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 181
    simpa using h
  have hprev := st264_p181
  have hstep := st264_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p183 : ((21228070427771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT264 (i+1))
      = (∑ i ∈ Finset.range 182, stT264 (i+1)) + stT264 183 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 182
    simpa using h
  have hprev := st264_p182
  have hstep := st264_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p184 : ((21649295431773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT264 (i+1))
      = (∑ i ∈ Finset.range 183, stT264 (i+1)) + stT264 184 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 183
    simpa using h
  have hprev := st264_p183
  have hstep := st264_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p185 : ((10555188109919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT264 (i+1))
      = (∑ i ∈ Finset.range 184, stT264 (i+1)) + stT264 185 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 184
    simpa using h
  have hprev := st264_p184
  have hstep := st264_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p186 : ((10268956972307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT264 (i+1))
      = (∑ i ∈ Finset.range 185, stT264 (i+1)) + stT264 186 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 185
    simpa using h
  have hprev := st264_p185
  have hstep := st264_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p187 : ((10450555210611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT264 (i+1))
      = (∑ i ∈ Finset.range 186, stT264 (i+1)) + stT264 187 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 186
    simpa using h
  have hprev := st264_p186
  have hstep := st264_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p188 : ((10792206309087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT264 (i+1))
      = (∑ i ∈ Finset.range 187, stT264 (i+1)) + stT264 188 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 187
    simpa using h
  have hprev := st264_p187
  have hstep := st264_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p189 : ((10724660595107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT264 (i+1))
      = (∑ i ∈ Finset.range 188, stT264 (i+1)) + stT264 189 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 188
    simpa using h
  have hprev := st264_p188
  have hstep := st264_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p190 : ((20723837660921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT264 (i+1))
      = (∑ i ∈ Finset.range 189, stT264 (i+1)) + stT264 190 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 189
    simpa using h
  have hprev := st264_p189
  have hstep := st264_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p191 : ((20597201905871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT264 (i+1))
      = (∑ i ∈ Finset.range 190, stT264 (i+1)) + stT264 191 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 190
    simpa using h
  have hprev := st264_p190
  have hstep := st264_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p192 : ((21270512782887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT264 (i+1))
      = (∑ i ∈ Finset.range 191, stT264 (i+1)) + stT264 192 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 191
    simpa using h
  have hprev := st264_p191
  have hstep := st264_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p193 : ((21657367277227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT264 (i+1))
      = (∑ i ∈ Finset.range 192, stT264 (i+1)) + stT264 193 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 192
    simpa using h
  have hprev := st264_p192
  have hstep := st264_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p194 : ((21143852846149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT264 (i+1))
      = (∑ i ∈ Finset.range 193, stT264 (i+1)) + stT264 194 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 193
    simpa using h
  have hprev := st264_p193
  have hstep := st264_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p195 : ((5136540983011/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT264 (i+1))
      = (∑ i ∈ Finset.range 194, stT264 (i+1)) + stT264 195 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 194
    simpa using h
  have hprev := st264_p194
  have hstep := st264_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p196 : ((20799771535579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT264 (i+1))
      = (∑ i ∈ Finset.range 195, stT264 (i+1)) + stT264 196 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 195
    simpa using h
  have hprev := st264_p195
  have hstep := st264_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p197 : ((21505651188079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT264 (i+1))
      = (∑ i ∈ Finset.range 196, stT264 (i+1)) + stT264 197 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 196
    simpa using h
  have hprev := st264_p196
  have hstep := st264_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p198 : ((1078769421319/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT264 (i+1))
      = (∑ i ∈ Finset.range 197, stT264 (i+1)) + stT264 198 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 197
    simpa using h
  have hprev := st264_p197
  have hstep := st264_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p199 : ((1306678233533/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT264 (i+1))
      = (∑ i ∈ Finset.range 198, stT264 (i+1)) + stT264 199 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 198
    simpa using h
  have hprev := st264_p198
  have hstep := st264_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p200 : ((20515379623653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT264 (i+1))
      = (∑ i ∈ Finset.range 199, stT264 (i+1)) + stT264 200 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 199
    simpa using h
  have hprev := st264_p199
  have hstep := st264_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p201 : ((20985757275873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT264 (i+1))
      = (∑ i ∈ Finset.range 200, stT264 (i+1)) + stT264 201 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 200
    simpa using h
  have hprev := st264_p200
  have hstep := st264_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p202 : ((5403301872637/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT264 (i+1))
      = (∑ i ∈ Finset.range 201, stT264 (i+1)) + stT264 202 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 201
    simpa using h
  have hprev := st264_p201
  have hstep := st264_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p203 : ((21472119692151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT264 (i+1))
      = (∑ i ∈ Finset.range 202, stT264 (i+1)) + stT264 203 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 202
    simpa using h
  have hprev := st264_p202
  have hstep := st264_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p204 : ((20773715041831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT264 (i+1))
      = (∑ i ∈ Finset.range 203, stT264 (i+1)) + stT264 204 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 203
    simpa using h
  have hprev := st264_p203
  have hstep := st264_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p205 : ((5133385171211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT264 (i+1))
      = (∑ i ∈ Finset.range 204, stT264 (i+1)) + stT264 205 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 204
    simpa using h
  have hprev := st264_p204
  have hstep := st264_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p206 : ((21093553071521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT264 (i+1))
      = (∑ i ∈ Finset.range 205, stT264 (i+1)) + stT264 206 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 205
    simpa using h
  have hprev := st264_p205
  have hstep := st264_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p207 : ((21650457501329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT264 (i+1))
      = (∑ i ∈ Finset.range 206, stT264 (i+1)) + stT264 207 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 206
    simpa using h
  have hprev := st264_p206
  have hstep := st264_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p208 : ((4283467649949/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT264 (i+1))
      = (∑ i ∈ Finset.range 207, stT264 (i+1)) + stT264 208 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 207
    simpa using h
  have hprev := st264_p207
  have hstep := st264_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p209 : ((1036304715383/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT264 (i+1))
      = (∑ i ∈ Finset.range 208, stT264 (i+1)) + stT264 209 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 208
    simpa using h
  have hprev := st264_p208
  have hstep := st264_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p210 : ((1283774760433/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT264 (i+1))
      = (∑ i ∈ Finset.range 209, stT264 (i+1)) + stT264 210 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 209
    simpa using h
  have hprev := st264_p209
  have hstep := st264_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p211 : ((5278192415779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT264 (i+1))
      = (∑ i ∈ Finset.range 210, stT264 (i+1)) + stT264 211 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 210
    simpa using h
  have hprev := st264_p210
  have hstep := st264_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p212 : ((1353478269001/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT264 (i+1))
      = (∑ i ∈ Finset.range 211, stT264 (i+1)) + stT264 212 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 211
    simpa using h
  have hprev := st264_p211
  have hstep := st264_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p213 : ((21433111824273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT264 (i+1))
      = (∑ i ∈ Finset.range 212, stT264 (i+1)) + stT264 213 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 212
    simpa using h
  have hprev := st264_p212
  have hstep := st264_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p214 : ((20749495746489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT264 (i+1))
      = (∑ i ∈ Finset.range 213, stT264 (i+1)) + stT264 214 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 213
    simpa using h
  have hprev := st264_p213
  have hstep := st264_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p215 : ((20519749362859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT264 (i+1))
      = (∑ i ∈ Finset.range 214, stT264 (i+1)) + stT264 215 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 214
    simpa using h
  have hprev := st264_p214
  have hstep := st264_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p216 : ((10522398089013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT264 (i+1))
      = (∑ i ∈ Finset.range 215, stT264 (i+1)) + stT264 216 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 215
    simpa using h
  have hprev := st264_p215
  have hstep := st264_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p217 : ((10815216769569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT264 (i+1))
      = (∑ i ∈ Finset.range 216, stT264 (i+1)) + stT264 217 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 216
    simpa using h
  have hprev := st264_p216
  have hstep := st264_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p218 : ((10756868580669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT264 (i+1))
      = (∑ i ∈ Finset.range 217, stT264 (i+1)) + stT264 218 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 217
    simpa using h
  have hprev := st264_p217
  have hstep := st264_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p219 : ((65156417661/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT264 (i+1))
      = (∑ i ∈ Finset.range 218, stT264 (i+1)) + stT264 219 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 218
    simpa using h
  have hprev := st264_p218
  have hstep := st264_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p220 : ((128083272777/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT264 (i+1))
      = (∑ i ∈ Finset.range 219, stT264 (i+1)) + stT264 220 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 219
    simpa using h
  have hprev := st264_p219
  have hstep := st264_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p221 : ((130593096093/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT264 (i+1))
      = (∑ i ∈ Finset.range 220, stT264 (i+1)) + stT264 221 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 220
    simpa using h
  have hprev := st264_p220
  have hstep := st264_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p222 : ((5385828320189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT264 (i+1))
      = (∑ i ∈ Finset.range 221, stT264 (i+1)) + stT264 222 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 221
    simpa using h
  have hprev := st264_p221
  have hstep := st264_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p223 : ((2703215035837/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT264 (i+1))
      = (∑ i ∈ Finset.range 222, stT264 (i+1)) + stT264 223 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 222
    simpa using h
  have hprev := st264_p222
  have hstep := st264_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p224 : ((52608854177/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT264 (i+1))
      = (∑ i ∈ Finset.range 223, stT264 (i+1)) + stT264 224 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 223
    simpa using h
  have hprev := st264_p223
  have hstep := st264_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p225 : ((10259028704029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT264 (i+1))
      = (∑ i ∈ Finset.range 224, stT264 (i+1)) + stT264 225 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 224
    simpa using h
  have hprev := st264_p224
  have hstep := st264_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p226 : ((5172720936977/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT264 (i+1))
      = (∑ i ∈ Finset.range 225, stT264 (i+1)) + stT264 226 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 225
    simpa using h
  have hprev := st264_p225
  have hstep := st264_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p227 : ((21347861331059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT264 (i+1))
      = (∑ i ∈ Finset.range 226, stT264 (i+1)) + stT264 227 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 226
    simpa using h
  have hprev := st264_p226
  have hstep := st264_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p228 : ((4339101719207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT264 (i+1))
      = (∑ i ∈ Finset.range 227, stT264 (i+1)) + stT264 228 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 227
    simpa using h
  have hprev := st264_p227
  have hstep := st264_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p229 : ((2132089360903/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT264 (i+1))
      = (∑ i ∈ Finset.range 228, stT264 (i+1)) + stT264 229 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 228
    simpa using h
  have hprev := st264_p228
  have hstep := st264_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p230 : ((20672394373673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT264 (i+1))
      = (∑ i ∈ Finset.range 229, stT264 (i+1)) + stT264 230 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 229
    simpa using h
  have hprev := st264_p229
  have hstep := st264_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p231 : ((20513883867593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT264 (i+1))
      = (∑ i ∈ Finset.range 230, stT264 (i+1)) + stT264 231 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 230
    simpa using h
  have hprev := st264_p230
  have hstep := st264_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p232 : ((21026951808017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT264 (i+1))
      = (∑ i ∈ Finset.range 231, stT264 (i+1)) + stT264 232 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 231
    simpa using h
  have hprev := st264_p231
  have hstep := st264_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p233 : ((10806707080927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT264 (i+1))
      = (∑ i ∈ Finset.range 232, stT264 (i+1)) + stT264 233 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 232
    simpa using h
  have hprev := st264_p232
  have hstep := st264_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p234 : ((10799615515519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT264 (i+1))
      = (∑ i ∈ Finset.range 233, stT264 (i+1)) + stT264 234 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 233
    simpa using h
  have hprev := st264_p233
  have hstep := st264_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p235 : ((21004457671037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT264 (i+1))
      = (∑ i ∈ Finset.range 234, stT264 (i+1)) + stT264 235 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 234
    simpa using h
  have hprev := st264_p234
  have hstep := st264_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p236 : ((10252790942661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT264 (i+1))
      = (∑ i ∈ Finset.range 235, stT264 (i+1)) + stT264 236 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 235
    simpa using h
  have hprev := st264_p235
  have hstep := st264_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p237 : ((413238818769/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT264 (i+1))
      = (∑ i ∈ Finset.range 236, stT264 (i+1)) + stT264 237 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 236
    simpa using h
  have hprev := st264_p236
  have hstep := st264_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p238 : ((21295038863941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT264 (i+1))
      = (∑ i ∈ Finset.range 237, stT264 (i+1)) + stT264 238 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 237
    simpa using h
  have hprev := st264_p237
  have hstep := st264_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p239 : ((4340342059459/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT264 (i+1))
      = (∑ i ∈ Finset.range 238, stT264 (i+1)) + stT264 239 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 238
    simpa using h
  have hprev := st264_p238
  have hstep := st264_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p240 : ((21437078064227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT264 (i+1))
      = (∑ i ∈ Finset.range 239, stT264 (i+1)) + stT264 240 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 239
    simpa using h
  have hprev := st264_p239
  have hstep := st264_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p241 : ((20793717242279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT264 (i+1))
      = (∑ i ∈ Finset.range 240, stT264 (i+1)) + stT264 241 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 240
    simpa using h
  have hprev := st264_p240
  have hstep := st264_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p242 : ((10234816259377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT264 (i+1))
      = (∑ i ∈ Finset.range 241, stT264 (i+1)) + stT264 242 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 241
    simpa using h
  have hprev := st264_p241
  have hstep := st264_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p243 : ((10405262167877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT264 (i+1))
      = (∑ i ∈ Finset.range 242, stT264 (i+1)) + stT264 243 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 242
    simpa using h
  have hprev := st264_p242
  have hstep := st264_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p244 : ((10724469113497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT264 (i+1))
      = (∑ i ∈ Finset.range 243, stT264 (i+1)) + stT264 244 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 243
    simpa using h
  have hprev := st264_p243
  have hstep := st264_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p245 : ((10853931585013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT264 (i+1))
      = (∑ i ∈ Finset.range 244, stT264 (i+1)) + stT264 245 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 244
    simpa using h
  have hprev := st264_p244
  have hstep := st264_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p246 : ((10658959263259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT264 (i+1))
      = (∑ i ∈ Finset.range 245, stT264 (i+1)) + stT264 246 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 245
    simpa using h
  have hprev := st264_p245
  have hstep := st264_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p247 : ((20689549548203/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT264 (i+1))
      = (∑ i ∈ Finset.range 246, stT264 (i+1)) + stT264 247 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 246
    simpa using h
  have hprev := st264_p246
  have hstep := st264_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p248 : ((20474219439101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT264 (i+1))
      = (∑ i ∈ Finset.range 247, stT264 (i+1)) + stT264 248 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 247
    simpa using h
  have hprev := st264_p247
  have hstep := st264_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p249 : ((20890363175837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT264 (i+1))
      = (∑ i ∈ Finset.range 248, stT264 (i+1)) + stT264 249 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 248
    simpa using h
  have hprev := st264_p248
  have hstep := st264_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_p250 : ((10754848948431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT264 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT264 (i+1))
      = (∑ i ∈ Finset.range 249, stT264 (i+1)) + stT264 250 := by
    have h := Finset.sum_range_succ (fun i => stT264 (i+1)) 249
    simpa using h
  have hprev := st264_p249
  have hstep := st264_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st264_s250 :
    |Real.sin (((264 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))
      - ((50597/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 509489/10000000) (δ := 13267/1000000000) (ψ := -29637/125000) 264 232
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 264`** (evaluated boundary). -/
theorem station_264_sign : hardyG ((((264:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 264 250 (by norm_num) (by norm_num)
    ((-29637/125000 : ℚ) : ℝ)
  have hchain := st264_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT264 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((264 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-29637/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st264_c250
  have hsinb := abs_le.mp st264_s250
  have hbdy_lo : ((-8527611298283/696962500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((264 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29637/125000 : ℚ) : ℝ))) / 2
          - ((((264:ℕ)):ℝ))
            * Real.sin (((264 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-29637/125000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((264:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((264:ℝ) * Real.log (250:ℝ) - ((-29637/125000 : ℚ) : ℝ))) / 2
        - ((264:ℝ)) * Real.sin ((264:ℝ) * Real.log (250:ℝ) - ((-29637/125000 : ℚ) : ℝ))
        ≥ ((-107866619/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((264:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-107866619/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-107866619/2000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-107866619/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((264:ℕ)):ℝ))+1) * (((((264:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((286237489879/187500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((10754848948431/5000000000000 : ℚ) : ℝ) + ((-8527611298283/696962500000000 : ℚ) : ℝ)
      - ((286237489879/187500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-29637/125000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((264:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-29637/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((264:ℕ)):ℝ)))).re
      - Real.sin ((-29637/125000 : ℚ) : ℝ)
        * (riemannZeta (line ((((264:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((264:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((264:ℕ)):ℝ))
      = (((((264:ℕ)):ℝ)) * (Real.log ((((264:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((264:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_264
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
  have hθwin : |(((-29637/125000 : ℚ) : ℝ) + ((58:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((264:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((264:ℕ)):ℝ)))
    (φ := ((-29637/125000 : ℚ) : ℝ) + ((58:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-29637/125000 : ℚ) : ℝ) + ((58:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-29637/125000 : ℚ)) : ℝ) - Real.pi) + ((58:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-29637/125000 : ℚ)) : ℝ) - Real.pi) 58).1,
    (cos_sin_shift ((((-29637/125000 : ℚ)) : ℝ) - Real.pi) 58).2]
  exact cos_sin_flip ((-29637/125000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_264_sign
end AxiomAudit
