import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 237` (rung-262.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT237 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((237 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((69893/250000 : ℚ) : ℝ))

theorem st237_c1 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((480587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69893/1000000) (δ := 1/1000000000) (ψ := 69893/250000) 237 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t1 : ((240281/250000 : ℚ) : ℝ) ≤ stT237 1 := by
  have hc : ((240281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240281/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((240281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c2 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((80597/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1583711/10000000) (δ := 2403/200000000) (ψ := 69893/250000) 237 26
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t2 : ((35616964479/62500000000 : ℚ) : ℝ) ≤ stT237 2 := by
  have hc : ((5037/6250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35616964479/62500000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((5037/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c3 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-197397/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3101167/5000000) (δ := 11907/1000000000) (ψ := 69893/250000) 237 41
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t3 : ((-2279488680957/5000000000000 : ℚ) : ℝ) ≤ stT237 3 := by
  have hc : ((-394819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2279488680957/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-394819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c4 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((24241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1933191/5000000) (δ := 3007/250000000) (ψ := 69893/250000) 237 52
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t4 : ((24191/2000000 : ℚ) : ℝ) ≤ stT237 4 := by
  have hc : ((24191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24191/2000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((24191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c5 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-519517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -165397/312500) (δ := 1483/125000000) (ψ := 69893/250000) 237 61
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t5 : ((-290446785639/1250000000000 : ℚ) : ℝ) ≤ stT237 5 := by
  have hc : ((-519567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290446785639/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-519567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c6 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-484157/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3611479/5000000) (δ := 1189/100000000) (ψ := 69893/250000) 237 68
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t6 : ((-988332391953/2500000000000 : ℚ) : ℝ) ≤ stT237 6 := by
  have hc : ((-242091/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-988332391953/2500000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-242091/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c7 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-122277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1114303/2000000) (δ := 11977/1000000000) (ψ := 69893/250000) 237 73
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t7 : ((-92440289623/400000000000 : ℚ) : ℝ) ≤ stT237 7 := by
  have hc : ((-122287/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92440289623/400000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-122287/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c8 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-194083/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6149053/10000000) (δ := 12041/1000000000) (ψ := 69893/250000) 237 78
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t8 : ((-686231239497/2500000000000 : ℚ) : ℝ) ≤ stT237 8 := by
  have hc : ((-388191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-686231239497/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-388191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c9 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((126181/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -520867/2000000) (δ := 11997/1000000000) (ψ := 69893/250000) 237 83
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t9 : ((841123249221/5000000000000 : ℚ) : ℝ) ≤ stT237 9 := by
  have hc : ((252337/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((841123249221/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((252337/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c10 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((5603/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -752523/2500000) (δ := 5963/500000000) (ψ := 69893/250000) 237 87
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t10 : ((566904560067/5000000000000 : ℚ) : ℝ) ≤ stT237 10 := by
  have hc : ((179271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((566904560067/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((179271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c11 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-51347/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 198041/312500) (δ := 753/62500000) (ψ := 69893/250000) 237 90
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t11 : ((-619305923157/2500000000000 : ℚ) : ℝ) ≤ stT237 11 := by
  have hc : ((-410801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-619305923157/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-410801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c12 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-394311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4940287/10000000) (δ := 2969/250000000) (ψ := 69893/250000) 237 94
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t12 : ((-35575700171/312500000000 : ℚ) : ℝ) ≤ stT237 12 := by
  have hc : ((-394361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35575700171/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-394361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c13 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-140461/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4638877/10000000) (δ := 5949/500000000) (ψ := 69893/250000) 237 97
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t13 : ((-194819030743/2500000000000 : ℚ) : ℝ) ≤ stT237 13 := by
  have hc : ((-70243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194819030743/2500000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-70243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c14 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7853777/10000000) (δ := 2971/250000000) (ψ := 69893/250000) 237 100
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t14 : ((-53454932613/200000000000 : ℚ) : ℝ) ≤ stT237 14 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53454932613/200000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c15 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((800039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160859/1000000) (δ := 5967/500000000) (ψ := 69893/250000) 237 102
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t15 : ((516390499533/2500000000000 : ℚ) : ℝ) ≤ stT237 15 := by
  have hc : ((799989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((516390499533/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((799989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c16 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-121677/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7276239/10000000) (δ := 2987/250000000) (ψ := 69893/250000) 237 105
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t16 : ((-1216832986733/5000000000000 : ℚ) : ℝ) ≤ stT237 16 := by
  have hc : ((-486733/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1216832986733/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-486733/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c17 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((55713/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -277209/1000000) (δ := 11933/1000000000) (ψ := 69893/250000) 237 107
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t17 : ((135108700353/1250000000000 : ℚ) : ℝ) ≤ stT237 17 := by
  have hc : ((222827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135108700353/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((222827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c18 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((495867/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2513/78125) (δ := 749/62500000) (ψ := 69893/250000) 237 109
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t18 : ((292177625631/1250000000000 : ℚ) : ℝ) ≤ stT237 18 := by
  have hc : ((247921/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292177625631/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((247921/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c19 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((992941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11889/400000) (δ := 2381/200000000) (ψ := 69893/250000) 237 111
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t19 : ((2277847837887/10000000000000 : ℚ) : ℝ) ≤ stT237 19 := by
  have hc : ((992891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2277847837887/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((992891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c20 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((957967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727421/10000000) (δ := 11913/1000000000) (ψ := 69893/250000) 237 113
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t20 : ((2141966592439/10000000000000 : ℚ) : ℝ) ≤ stT237 20 := by
  have hc : ((957917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2141966592439/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((957917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c21 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((4269/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1617577/5000000) (δ := 11927/1000000000) (ψ := 69893/250000) 237 115
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t21 : ((149024208887/2500000000000 : ℚ) : ℝ) ≤ stT237 21 := by
  have hc : ((136583/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149024208887/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((136583/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c22 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-476713/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7087981/10000000) (δ := 11961/1000000000) (ψ := 69893/250000) 237 117
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t22 : ((-63525576869/312500000000 : ℚ) : ℝ) ≤ stT237 22 := by
  have hc : ((-238369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63525576869/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-238369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c23 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((9593/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 885437/2500000) (δ := 12049/1000000000) (ψ := 69893/250000) 237 118
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t23 : ((19996270317/625000000000 : ℚ) : ℝ) ≤ stT237 23 := by
  have hc : ((76719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19996270317/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((76719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c24 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((121553/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -166101/625000) (δ := 11863/1000000000) (ψ := 69893/250000) 237 120
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t24 : ((496186903521/5000000000000 : ℚ) : ℝ) ≤ stT237 24 := by
  have hc : ((243081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496186903521/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((243081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c25 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-137463/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363841/625000) (δ := 1197/100000000) (ψ := 69893/250000) 237 121
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t25 : ((-274946137473/2000000000000 : ℚ) : ℝ) ≤ stT237 25 := by
  have hc : ((-137473/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274946137473/2000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-137473/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c26 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((293891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1178103/5000000) (δ := 2377/200000000) (ψ := 69893/250000) 237 123
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t26 : ((288159269213/2500000000000 : ℚ) : ℝ) ≤ stT237 26 := by
  have hc : ((146933/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((288159269213/2500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((146933/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c27 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-147447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2148479/5000000) (δ := 12011/1000000000) (ψ := 69893/250000) 237 124
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t27 : ((-283858123997/10000000000000 : ℚ) : ℝ) ≤ stT237 27 := by
  have hc : ((-147497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283858123997/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-147497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c28 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-76407/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2785553/5000000) (δ := 11897/1000000000) (ψ := 69893/250000) 237 126
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t28 : ((-577630069419/5000000000000 : ℚ) : ℝ) ≤ stT237 28 := by
  have hc : ((-305653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-577630069419/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-305653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c29 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((19621/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -243737/5000000) (δ := 1189/100000000) (ψ := 69893/250000) 237 127
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t29 : ((1821670893/10000000000 : ℚ) : ℝ) ≤ stT237 29 := by
  have hc : ((981/1000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1821670893/10000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((981/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c30 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((2863/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1945601/5000000) (δ := 601/50000000) (ψ := 69893/250000) 237 128
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t30 : ((5208839073/2000000000000 : ℚ) : ℝ) ≤ stT237 30 := by
  have hc : ((2853/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5208839073/2000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((2853/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c31 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-99529/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3805627/5000000) (δ := 19/1600000) (ψ := 69893/250000) 237 129
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t31 : ((-44692109709/250000000000 : ℚ) : ℝ) ≤ stT237 31 := by
  have hc : ((-49767/50000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44692109709/250000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-49767/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c32 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-206903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156049/312500) (δ := 11961/1000000000) (ψ := 69893/250000) 237 131
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t32 : ((-22862530611/312500000000 : ℚ) : ℝ) ≤ stT237 32 := by
  have hc : ((-12933/31250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22862530611/312500000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-12933/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c33 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((22023/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1234679/5000000) (δ := 5927/500000000) (ψ := 69893/250000) 237 132
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t33 : ((4791703537/50000000000 : ℚ) : ℝ) ≤ stT237 33 := by
  have hc : ((22021/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4791703537/50000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((22021/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c34 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((980899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489419/10000000) (δ := 11947/1000000000) (ψ := 69893/250000) 237 133
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t34 : ((336428264453/2000000000000 : ℚ) : ℝ) ≤ stT237 34 := by
  have hc : ((980849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336428264453/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((980849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c35 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((57781/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 61107/625000) (δ := 2991/250000000) (ψ := 69893/250000) 237 134
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t35 : ((195324808671/1250000000000 : ℚ) : ℝ) ≤ stT237 35 := by
  have hc : ((462223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195324808671/1250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((462223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c36 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((70781/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1961007/10000000) (δ := 11971/1000000000) (ψ := 69893/250000) 237 135
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t36 : ((7372497051/62500000000 : ℚ) : ℝ) ≤ stT237 36 := by
  have hc : ((8847/12500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7372497051/62500000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((8847/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c37 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((544687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2486951/10000000) (δ := 5939/500000000) (ψ := 69893/250000) 237 136
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t37 : ((895377236993/10000000000000 : ℚ) : ℝ) ≤ stT237 37 := by
  have hc : ((544637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((895377236993/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((544637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c38 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((513139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 322487/1250000) (δ := 5959/500000000) (ψ := 69893/250000) 237 137
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t38 : ((416170079523/5000000000000 : ℚ) : ℝ) ≤ stT237 38 := by
  have hc : ((513089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((416170079523/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((513089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c39 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((38607/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2262417/10000000) (δ := 1499/125000000) (ψ := 69893/250000) 237 138
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t39 : ((494525212511/5000000000000 : ℚ) : ℝ) ≤ stT237 39 := by
  have hc : ((308831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((494525212511/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((308831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c40 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((50791/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6221/40000) (δ := 11899/1000000000) (ψ := 69893/250000) 237 139
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t40 : ((321210556407/2500000000000 : ℚ) : ℝ) ≤ stT237 40 := by
  have hc : ((406303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((321210556407/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((406303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c41 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((981803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 119413/2500000) (δ := 1487/125000000) (ψ := 69893/250000) 237 140
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t41 : ((1533239984961/10000000000000 : ℚ) : ℝ) ≤ stT237 41 := by
  have hc : ((981753/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1533239984961/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((981753/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c42 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((116037/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -952483/10000000) (δ := 5957/500000000) (ψ := 69893/250000) 237 141
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t42 : ((716157105059/5000000000000 : ℚ) : ℝ) ≤ stT237 42 := by
  have hc : ((464123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((716157105059/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((464123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c43 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((92949/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21749/80000) (δ := 11921/1000000000) (ψ := 69893/250000) 237 142
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t43 : ((28346116183/400000000000 : ℚ) : ℝ) ≤ stT237 43 := by
  have hc : ((92939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28346116183/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((92939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c44 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-68829/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -480531/1000000) (δ := 479/40000000) (ψ := 69893/250000) 237 143
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t44 : ((-103778716323/2000000000000 : ℚ) : ℝ) ≤ stT237 44 := by
  have hc : ((-68839/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103778716323/2000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-68839/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c45 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-965787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7198139/10000000) (δ := 2967/250000000) (ψ := 69893/250000) 237 144
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t45 : ((-179973100743/1250000000000 : ℚ) : ℝ) ≤ stT237 45 := by
  have hc : ((-965837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179973100743/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-965837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c46 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-344079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5824359/10000000) (δ := 187/15625000) (ψ := 69893/250000) 237 144
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t46 : ((-3170961373/31250000000 : ℚ) : ℝ) ≤ stT237 46 := by
  have hc : ((-43013/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3170961373/31250000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-43013/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c47 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((82873/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2858879/10000000) (δ := 11943/1000000000) (ψ := 69893/250000) 237 145
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t47 : ((120868032087/2000000000000 : ℚ) : ℝ) ≤ stT237 47 := by
  have hc : ((82863/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120868032087/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((82863/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c48 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((494387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74989/2000000) (δ := 11853/1000000000) (ψ := 69893/250000) 237 146
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t48 : ((2854199007/20000000000 : ℚ) : ℝ) ≤ stT237 48 := by
  have hc : ((247181/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2854199007/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((247181/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c49 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((24381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241627/625000) (δ := 11957/1000000000) (ψ := 69893/250000) 237 147
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t49 : ((34758561001/10000000000000 : ℚ) : ℝ) ≤ stT237 49 := by
  have hc : ((24331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34758561001/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((24331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c50 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-497499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7603837/10000000) (δ := 12039/1000000000) (ψ := 69893/250000) 237 148
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t50 : ((-87950675767/625000000000 : ℚ) : ℝ) ≤ stT237 50 := by
  have hc : ((-124381/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87950675767/625000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-124381/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c51 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-80797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1032301/2500000) (δ := 1483/125000000) (ψ := 69893/250000) 237 148
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t51 : ((-113208518007/10000000000000 : ℚ) : ℝ) ≤ stT237 51 := by
  have hc : ((-80847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113208518007/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-80847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c52 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((999567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -14707/2000000) (δ := 11871/1000000000) (ψ := 69893/250000) 237 149
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t52 : ((5544320799/40000000000 : ℚ) : ℝ) ≤ stT237 52 := by
  have hc : ((999517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5544320799/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((999517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c53 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-9017/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56193/125000) (δ := 477/40000000) (ψ := 69893/250000) 237 150
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t53 : ((-6194276257/200000000000 : ℚ) : ℝ) ≤ stT237 53 := by
  have hc : ((-9019/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6194276257/200000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-9019/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c54 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-872871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6579629/10000000) (δ := 481/40000000) (ψ := 69893/250000) 237 150
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t54 : ((-296973834647/2500000000000 : ℚ) : ℝ) ≤ stT237 54 := by
  have hc : ((-872921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296973834647/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-872921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c55 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((766513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 435877/2500000) (δ := 5943/500000000) (ψ := 69893/250000) 237 151
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t55 : ((1033497942737/10000000000000 : ℚ) : ℝ) ≤ stT237 55 := by
  have hc : ((766463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1033497942737/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((766463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c56 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((252631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1644247/5000000) (δ := 11893/1000000000) (ψ := 69893/250000) 237 152
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t56 : ((168762752893/5000000000000 : ℚ) : ℝ) ≤ stT237 56 := by
  have hc : ((252581/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168762752893/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((252581/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c57 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-482913/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7198519/10000000) (δ := 11893/1000000000) (ψ := 69893/250000) 237 152
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t57 : ((-319833658977/2500000000000 : ℚ) : ℝ) ≤ stT237 57 := by
  have hc : ((-241469/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319833658977/2500000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-241469/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c58 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((753071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1795197/10000000) (δ := 11903/1000000000) (ψ := 69893/250000) 237 153
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t58 : ((123595595793/1250000000000 : ℚ) : ℝ) ≤ stT237 58 := by
  have hc : ((753021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123595595793/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((753021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c59 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((7129/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1892167/5000000) (δ := 11907/1000000000) (ψ := 69893/250000) 237 154
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t59 : ((37092119499/5000000000000 : ℚ) : ℝ) ≤ stT237 59 := by
  have hc : ((28491/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37092119499/5000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((28491/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c60 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-782551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6173873/10000000) (δ := 12007/1000000000) (ψ := 69893/250000) 237 154
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t60 : ((-202066795599/2000000000000 : ℚ) : ℝ) ≤ stT237 60 := by
  have hc : ((-782601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202066795599/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-782601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c61 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((994617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811/31250) (δ := 6007/500000000) (ψ := 69893/250000) 237 155
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t61 : ((79588235041/625000000000 : ℚ) : ℝ) ≤ stT237 61 := by
  have hc : ((994567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79588235041/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((994567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c62 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-342587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5814097/10000000) (δ := 6011/500000000) (ψ := 69893/250000) 237 156
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t62 : ((-54389740653/625000000000 : ℚ) : ℝ) ≤ stT237 62 := by
  have hc : ((-85653/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54389740653/625000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-85653/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c63 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((104151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183307/500000) (δ := 6011/500000000) (ψ := 69893/250000) 237 156
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t63 : ((131154871981/10000000000000 : ℚ) : ℝ) ≤ stT237 63 := by
  have hc : ((104101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131154871981/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((104101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c64 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((467459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -677739/2500000) (δ := 5937/500000000) (ψ := 69893/250000) 237 157
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t64 : ((467409/8000000 : ℚ) : ℝ) ≤ stT237 64 := by
  have hc : ((467409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((467409/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((467409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c65 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-3407/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6475283/10000000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 157
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t65 : ((-1320660533/12500000000 : ℚ) : ℝ) ≤ stT237 65 := by
  have hc : ((-4259/5000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1320660533/12500000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-4259/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c66 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((997213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186687/10000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 158
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t66 : ((613710948491/5000000000000 : ℚ) : ℝ) ≤ stT237 66 := by
  have hc : ((997163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((613710948491/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((997163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c67 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-470077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3492347/5000000) (δ := 12043/1000000000) (ψ := 69893/250000) 237 159
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t67 : ((-57432126289/500000000000 : ℚ) : ℝ) ≤ stT237 67 := by
  have hc : ((-235051/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57432126289/500000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-235051/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c68 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((753583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448313/2500000) (δ := 299/25000000) (ψ := 69893/250000) 237 159
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t68 : ((456896445687/5000000000000 : ℚ) : ℝ) ≤ stT237 68 := by
  have hc : ((753533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((456896445687/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((753533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c69 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-509989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2632461/5000000) (δ := 11853/1000000000) (ψ := 69893/250000) 237 160
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t69 : ((-614015040501/10000000000000 : ℚ) : ℝ) ≤ stT237 69 := by
  have hc : ((-510039/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-614015040501/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-510039/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c70 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((52699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3260383/10000000) (δ := 239/20000000) (ψ := 69893/250000) 237 160
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t70 : ((15743842023/500000000000 : ℚ) : ℝ) ≤ stT237 70 := by
  have hc : ((52689/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15743842023/500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((52689/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c71 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-46469/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -808641/2000000) (δ := 11857/1000000000) (ψ := 69893/250000) 237 161
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t71 : ((-27603955929/5000000000000 : ℚ) : ℝ) ≤ stT237 71 := by
  have hc : ((-46519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27603955929/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-46519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c72 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-1974/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2121839/5000000) (δ := 11957/1000000000) (ψ := 69893/250000) 237 161
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t72 : ((-4654606801/312500000000 : ℚ) : ℝ) ≤ stT237 72 := by
  have hc : ((-63193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4654606801/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-63193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c73 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((251369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -658351/2000000) (δ := 2393/200000000) (ψ := 69893/250000) 237 162
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t73 : ((294146522109/10000000000000 : ℚ) : ℝ) ≤ stT237 73 := by
  have hc : ((251319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((294146522109/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((251319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c74 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-66137/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4769563/10000000) (δ := 2393/200000000) (ψ := 69893/250000) 237 162
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t74 : ((-76894366119/2000000000000 : ℚ) : ℝ) ≤ stT237 74 := by
  have hc : ((-66147/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76894366119/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-66147/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c75 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((45983/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1492607/5000000) (δ := 11931/1000000000) (ψ := 69893/250000) 237 163
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t75 : ((2123574129/50000000000 : ℚ) : ℝ) ≤ stT237 75 := by
  have hc : ((183907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2123574129/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((183907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c76 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-91389/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4862567/10000000) (δ := 11931/1000000000) (ψ := 69893/250000) 237 163
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t76 : ((-209689482437/5000000000000 : ℚ) : ℝ) ≤ stT237 76 := by
  have hc : ((-182803/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209689482437/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-182803/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c77 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((324729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3100177/10000000) (δ := 2981/250000000) (ψ := 69893/250000) 237 164
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t77 : ((74001162359/2000000000000 : ℚ) : ℝ) ≤ stT237 77 := by
  have hc : ((324679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74001162359/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((324679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c78 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-30591/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71017/156250) (δ := 11979/1000000000) (ψ := 69893/250000) 237 164
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t78 : ((-69289186071/2500000000000 : ℚ) : ℝ) ≤ stT237 78 := by
  have hc : ((-122389/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69289186071/2500000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-122389/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c79 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((62233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1807509/5000000) (δ := 5943/500000000) (ψ := 69893/250000) 237 165
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t79 : ((273396141/19531250000 : ℚ) : ℝ) ≤ stT237 79 := by
  have hc : ((1944/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273396141/19531250000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((1944/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c80 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((1781/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3837921/10000000) (δ := 5943/500000000) (ψ := 69893/250000) 237 165
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t80 : ((3976843381/1000000000000 : ℚ) : ℝ) ≤ stT237 80 := by
  have hc : ((3557/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3976843381/1000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((3557/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c81 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-230983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4509711/10000000) (δ := 11893/1000000000) (ψ := 69893/250000) 237 166
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t81 : ((-32087942337/1250000000000 : ℚ) : ℝ) ≤ stT237 81 := by
  have hc : ((-231033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32087942337/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-231033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c82 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((56239/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2760323/10000000) (δ := 1191/100000000) (ψ := 69893/250000) 237 166
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t82 : ((49678935453/1000000000000 : ℚ) : ℝ) ≤ stT237 82 := by
  have hc : ((224931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49678935453/1000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((224931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c83 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-670949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5765711/10000000) (δ := 12003/1000000000) (ψ := 69893/250000) 237 167
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t83 : ((-736517355357/10000000000000 : ℚ) : ℝ) ≤ stT237 83 := by
  have hc : ((-670999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-736517355357/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-670999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c84 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((430881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 665079/5000000) (δ := 23803/1000000000) (ψ := 69893/250000) 237 167
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t84 : ((58762780273/625000000000 : ℚ) : ℝ) ≤ stT237 84 := by
  have hc : ((53857/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58762780273/625000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((53857/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c85 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-490501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7365893/10000000) (δ := 1501/125000000) (ψ := 69893/250000) 237 168
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t85 : ((-266025248739/2500000000000 : ℚ) : ℝ) ≤ stT237 85 := by
  have hc : ((-245263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-266025248739/2500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-245263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c86 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((98483/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -436013/10000000) (δ := 1501/125000000) (ψ := 69893/250000) 237 168
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t86 : ((53095743153/500000000000 : ℚ) : ℝ) ≤ stT237 86 := by
  have hc : ((49239/50000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53095743153/500000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((49239/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c87 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-838613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 320691/500000) (δ := 2977/250000000) (ψ := 69893/250000) 237 168
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t87 : ((-899141504919/10000000000000 : ℚ) : ℝ) ≤ stT237 87 := by
  have hc : ((-838663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-899141504919/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-838663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c88 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((26633/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2522639/10000000) (δ := 2997/250000000) (ψ := 69893/250000) 237 169
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t88 : ((56776385783/1000000000000 : ℚ) : ℝ) ≤ stT237 88 := by
  have hc : ((53261/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56776385783/1000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((53261/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c89 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-24493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 834463/2000000) (δ := 743/62500000) (ψ := 69893/250000) 237 169
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t89 : ((-25975780989/2500000000000 : ℚ) : ℝ) ≤ stT237 89 := by
  have hc : ((-49011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25975780989/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-49011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c90 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-385169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1228867/2500000) (δ := 11881/1000000000) (ψ := 69893/250000) 237 170
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t90 : ((-406056651367/10000000000000 : ℚ) : ℝ) ≤ stT237 90 := by
  have hc : ((-385219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-406056651367/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-385219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c91 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((794491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101973/625000) (δ := 23781/1000000000) (ψ := 69893/250000) 237 170
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t91 : ((208199947311/2500000000000 : ℚ) : ℝ) ≤ stT237 91 := by
  have hc : ((794441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((208199947311/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((794441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c92 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-497441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7600933/10000000) (δ := 5937/500000000) (ψ := 69893/250000) 237 171
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t92 : ((-259322310009/2500000000000 : ℚ) : ℝ) ≤ stT237 92 := by
  have hc : ((-248733/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-259322310009/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-248733/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c93 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((887829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47819/400000) (δ := 5987/500000000) (ψ := 69893/250000) 237 171
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t93 : ((920583321829/10000000000000 : ℚ) : ℝ) ≤ stT237 93 := by
  have hc : ((887779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((920583321829/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((887779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c94 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-116729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5141491/10000000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 171
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t94 : ((-120409751413/2500000000000 : ℚ) : ℝ) ≤ stT237 94 := by
  have hc : ((-233483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120409751413/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-233483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c95 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-147297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2148289/5000000) (δ := 3009/250000000) (ψ := 69893/250000) 237 172
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t95 : ((-151174927713/10000000000000 : ℚ) : ℝ) ≤ stT237 95 := by
  have hc : ((-147347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151174927713/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-147347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c96 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((4517/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1907667/10000000) (δ := 373/31250000) (ψ := 69893/250000) 237 172
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t96 : ((3687857277/50000000000 : ℚ) : ℝ) ≤ stT237 96 := by
  have hc : ((72267/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3687857277/50000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((72267/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c97 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-498501/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7660337/10000000) (δ := 3011/250000000) (ψ := 69893/250000) 237 173
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t97 : ((-253088439261/2500000000000 : ℚ) : ℝ) ≤ stT237 97 := by
  have hc : ((-249263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253088439261/2500000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-249263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c98 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((806053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1583361/10000000) (δ := 1493/125000000) (ψ := 69893/250000) 237 173
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t98 : ((101773192807/1250000000000 : ℚ) : ℝ) ≤ stT237 98 := by
  have hc : ((806003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101773192807/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((806003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c99 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-6269/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69249/156250) (δ := 1493/125000000) (ψ := 69893/250000) 237 173
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t99 : ((-50417228751/2500000000000 : ℚ) : ℝ) ≤ stT237 99 := by
  have hc : ((-100329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50417228751/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-100329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c100 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-529231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -212849/400000) (δ := 747/62500000) (ψ := 69893/250000) 237 174
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t100 : ((-529281/10000000 : ℚ) : ℝ) ≤ stT237 100 := by
  have hc : ((-529281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-529281/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-529281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c101 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((486861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 574387/10000000) (δ := 747/62500000) (ψ := 69893/250000) 237 174
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t101 : ((121104958233/1250000000000 : ℚ) : ℝ) ≤ stT237 101 := by
  have hc : ((121709/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((121104958233/1250000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((121709/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c102 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-838189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10259/16000) (δ := 2963/250000000) (ψ := 69893/250000) 237 174
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t102 : ((-207495167343/2500000000000 : ℚ) : ℝ) ≤ stT237 102 := by
  have hc : ((-838239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207495167343/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-838239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c103 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((32763/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3515599/10000000) (δ := 5929/500000000) (ψ := 69893/250000) 237 175
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t103 : ((32272480737/2000000000000 : ℚ) : ℝ) ≤ stT237 103 := by
  have hc : ((32753/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32272480737/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((32753/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c104 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((634349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2209077/10000000) (δ := 5979/500000000) (ψ := 69893/250000) 237 175
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t104 : ((31099045671/500000000000 : ℚ) : ℝ) ≤ stT237 104 := by
  have hc : ((634299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31099045671/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((634299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c105 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-19999/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3914479/5000000) (δ := 5969/500000000) (ψ := 69893/250000) 237 176
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t105 : ((-975901/10000000 : ℚ) : ℝ) ≤ stT237 105 := by
  have hc : ((-1 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-975901/10000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-1 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c106 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((158297/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -553207/2500000) (δ := 2373/200000000) (ψ := 69893/250000) 237 176
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t106 : ((61495744233/1000000000000 : ℚ) : ℝ) ≤ stT237 106 := by
  have hc : ((316569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61495744233/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((316569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c107 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((57127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 837657/2500000) (δ := 6019/500000000) (ψ := 69893/250000) 237 176
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t107 : ((6901830409/312500000000 : ℚ) : ℝ) ≤ stT237 107 := by
  have hc : ((114229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6901830409/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((114229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c108 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-11497/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6845663/10000000) (δ := 11931/1000000000) (ψ := 69893/250000) 237 177
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t108 : ((-88508809231/1000000000000 : ℚ) : ℝ) ≤ stT237 108 := by
  have hc : ((-91981/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88508809231/1000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-91981/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c109 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((850463/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1384827/10000000) (δ := 2993/250000000) (ψ := 69893/250000) 237 177
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t109 : ((407273841069/5000000000000 : ℚ) : ℝ) ≤ stT237 109 := by
  have hc : ((850413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((407273841069/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((850413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c110 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-7933/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4026179/10000000) (δ := 371/31250000) (ψ := 69893/250000) 237 177
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t110 : ((-7573356609/2000000000000 : ℚ) : ℝ) ≤ stT237 110 := by
  have hc : ((-7943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7573356609/2000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-7943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c111 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-10219/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6319719/10000000) (δ := 1503/125000000) (ψ := 69893/250000) 237 178
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t111 : ((-38800155303/500000000000 : ℚ) : ℝ) ≤ stT237 111 := by
  have hc : ((-81757/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38800155303/500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-81757/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c112 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((920151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1005823/10000000) (δ := 11879/1000000000) (ψ := 69893/250000) 237 178
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t112 : ((869413556011/10000000000000 : ℚ) : ℝ) ≤ stT237 112 := by
  have hc : ((920101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((869413556011/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((920101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c113 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-13317/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4260909/10000000) (δ := 1503/125000000) (ψ := 69893/250000) 237 178
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t113 : ((-6266142581/500000000000 : ℚ) : ℝ) ≤ stT237 113 := by
  have hc : ((-6661/50000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6266142581/500000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-6661/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c114 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-795549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6226773/10000000) (δ := 11987/1000000000) (ψ := 69893/250000) 237 179
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t114 : ((-372573442507/5000000000000 : ℚ) : ℝ) ≤ stT237 114 := by
  have hc : ((-795599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-372573442507/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-795599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c115 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((912753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -131507/1250000) (δ := 11887/1000000000) (ψ := 69893/250000) 237 179
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t115 : ((106387399789/1250000000000 : ℚ) : ℝ) ≤ stT237 115 := by
  have hc : ((912703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106387399789/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((912703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c116 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-60291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4077809/10000000) (δ := 11887/1000000000) (ψ := 69893/250000) 237 179
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t116 : ((-56025230657/10000000000000 : ℚ) : ℝ) ≤ stT237 116 := by
  have hc : ((-60341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56025230657/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-60341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c117 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-865879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6544253/10000000) (δ := 11909/1000000000) (ψ := 69893/250000) 237 180
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t117 : ((-800552226429/10000000000000 : ℚ) : ℝ) ≤ stT237 117 := by
  have hc : ((-865929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-800552226429/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-865929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c118 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((2578/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1501663/10000000) (δ := 5947/500000000) (ψ := 69893/250000) 237 180
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t118 : ((37969534917/500000000000 : ℚ) : ℝ) ≤ stT237 118 := by
  have hc : ((82491/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37969534917/500000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((82491/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c119 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((170627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1749163/5000000) (δ := 5947/500000000) (ψ := 69893/250000) 237 180
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t119 : ((78183797373/5000000000000 : ℚ) : ℝ) ≤ stT237 119 := by
  have hc : ((170577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78183797373/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((170577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c120 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-485547/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -362571/500000) (δ := 6001/500000000) (ψ := 69893/250000) 237 181
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t120 : ((-110816149303/1250000000000 : ℚ) : ℝ) ≤ stT237 120 := by
  have hc : ((-121393/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110816149303/1250000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-121393/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c121 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((297411/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2334381/10000000) (δ := 6001/500000000) (ψ := 69893/250000) 237 181
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t121 : ((13517531937/250000000000 : ℚ) : ℝ) ≤ stT237 121 := by
  have hc : ((148693/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13517531937/250000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((148693/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c122 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((21041/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2542191/10000000) (δ := 12001/1000000000) (ψ := 69893/250000) 237 181
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t122 : ((19047805923/400000000000 : ℚ) : ℝ) ≤ stT237 122 := by
  have hc : ((21039/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19047805923/400000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((21039/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c123 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-491001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3689473/5000000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 181
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t123 : ((-22137170671/250000000000 : ℚ) : ℝ) ≤ stT237 123 := by
  have hc : ((-245513/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22137170671/250000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-245513/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c124 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((157567/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1765713/5000000) (δ := 1501/125000000) (ψ := 69893/250000) 237 182
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t124 : ((70727180721/5000000000000 : ℚ) : ℝ) ≤ stT237 124 := by
  have hc : ((157517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70727180721/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((157517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c125 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((881833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 306913/2500000) (δ := 2379/200000000) (ψ := 69893/250000) 237 182
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t125 : ((788690523341/10000000000000 : ℚ) : ℝ) ≤ stT237 125 := by
  have hc : ((881783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((788690523341/10000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((881783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c126 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-72341/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5948811/10000000) (δ := 1501/125000000) (ψ := 69893/250000) 237 182
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t126 : ((-32225476683/500000000000 : ℚ) : ℝ) ≤ stT237 126 := by
  have hc : ((-36173/50000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32225476683/500000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-36173/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c127 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-443371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5075381/10000000) (δ := 743/62500000) (ψ := 69893/250000) 237 183
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t127 : ((-393472728297/10000000000000 : ℚ) : ℝ) ≤ stT237 127 := by
  have hc : ((-443421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393472728297/10000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-443421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c128 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((492681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -85657/2000000) (δ := 743/62500000) (ψ := 69893/250000) 237 183
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t128 : ((27215641453/312500000000 : ℚ) : ℝ) ≤ stT237 128 := by
  have hc : ((30791/31250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27215641453/312500000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((30791/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c129 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-102093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4182669/10000000) (δ := 2403/200000000) (ψ := 69893/250000) 237 183
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t129 : ((-89931906493/10000000000000 : ℚ) : ℝ) ≤ stT237 129 := by
  have hc : ((-102143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89931906493/10000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-102143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c130 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-116917/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -695001/1000000) (δ := 599/50000000) (ψ := 69893/250000) 237 184
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t130 : ((-410194354887/5000000000000 : ℚ) : ℝ) ≤ stT237 130 := by
  have hc : ((-467693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-410194354887/5000000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-467693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c131 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((142581/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2409741/10000000) (δ := 12023/1000000000) (ψ := 69893/250000) 237 184
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t131 : ((31140667181/625000000000 : ℚ) : ℝ) ≤ stT237 131 := by
  have hc : ((285137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31140667181/625000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((285137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c132 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((334329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 130999/625000) (δ := 297/25000000) (ψ := 69893/250000) 237 184
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t132 : ((2273235859/39062500000 : ℚ) : ℝ) ≤ stT237 132 := by
  have hc : ((10447/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2273235859/39062500000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((10447/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c133 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-870533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65677/100000) (δ := 297/25000000) (ψ := 69893/250000) 237 184
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t133 : ((-75489122513/1000000000000 : ℚ) : ℝ) ≤ stT237 133 := by
  have hc : ((-870583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75489122513/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-870583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c134 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-152541/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4702053/10000000) (δ := 2373/100000000) (ψ := 69893/250000) 237 185
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t134 : ((-65898518927/2500000000000 : ℚ) : ℝ) ≤ stT237 134 := by
  have hc : ((-76283/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65898518927/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-76283/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c135 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((992959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59369/2000000) (δ := 1193/100000000) (ψ := 69893/250000) 237 185
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t135 : ((427279522879/5000000000000 : ℚ) : ℝ) ≤ stT237 135 := by
  have hc : ((992909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((427279522879/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((992909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c136 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-29757/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 509483/1250000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 185
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t136 : ((-12768928263/2500000000000 : ℚ) : ℝ) ≤ stT237 136 := by
  have hc : ((-14891/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12768928263/2500000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-14891/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c137 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-194957/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1458277/2000000) (δ := 5933/500000000) (ψ := 69893/250000) 237 186
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t137 : ((-83285808093/1000000000000 : ℚ) : ℝ) ≤ stT237 137 := by
  have hc : ((-194967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83285808093/1000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-194967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c138 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((23059/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -298231/1000000) (δ := 11937/1000000000) (ψ := 69893/250000) 237 186
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t138 : ((19626451929/625000000000 : ℚ) : ℝ) ≤ stT237 138 := by
  have hc : ((184447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19626451929/625000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((184447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c139 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((868669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 647859/5000000) (δ := 12037/1000000000) (ψ := 69893/250000) 237 186
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t139 : ((184188053093/2500000000000 : ℚ) : ℝ) ≤ stT237 139 := by
  have hc : ((868619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((184188053093/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((868619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c140 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-602337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2771527/5000000) (δ := 11937/1000000000) (ψ := 69893/250000) 237 186
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t140 : ((-101822076997/2000000000000 : ℚ) : ℝ) ≤ stT237 140 := by
  have hc : ((-602387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101822076997/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-602387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c141 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-90393/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118957/200000) (δ := 11859/1000000000) (ψ := 69893/250000) 237 187
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t141 : ((-38064954593/625000000000 : ℚ) : ℝ) ≤ stT237 141 := by
  have hc : ((-361597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38064954593/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-361597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c142 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((762121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -880267/5000000) (δ := 11859/1000000000) (ψ := 69893/250000) 237 187
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t142 : ((639515503851/10000000000000 : ℚ) : ℝ) ≤ stT237 142 := by
  have hc : ((762071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((639515503851/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((762071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c143 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((287187/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1198697/5000000) (δ := 11859/1000000000) (ψ := 69893/250000) 237 187
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t143 : ((60034231301/1250000000000 : ℚ) : ℝ) ≤ stT237 143 := by
  have hc : ((143581/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60034231301/1250000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((143581/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c144 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-431131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652629/1000000) (δ := 3011/250000000) (ψ := 69893/250000) 237 187
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t144 : ((-44912119263/625000000000 : ℚ) : ℝ) ≤ stT237 144 := by
  have hc : ((-107789/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44912119263/625000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-107789/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c145 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-111371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5081277/10000000) (δ := 12051/1000000000) (ψ := 69893/250000) 237 188
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t145 : ((-36999593797/1000000000000 : ℚ) : ℝ) ≤ stT237 145 := by
  have hc : ((-222767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36999593797/1000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-222767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c146 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((22991/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252271/2500000) (δ := 11951/1000000000) (ψ := 69893/250000) 237 188
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t146 : ((15221145639/200000000000 : ℚ) : ℝ) ≤ stT237 146 := by
  have hc : ((91959/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15221145639/200000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((91959/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c147 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((43647/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1517631/5000000) (δ := 12051/1000000000) (ψ := 69893/250000) 237 188
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t147 : ((71988559259/2500000000000 : ℚ) : ℝ) ≤ stT237 147 := by
  have hc : ((174563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71988559259/2500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((174563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c148 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-189803/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3526117/5000000) (δ := 11951/1000000000) (ψ := 69893/250000) 237 188
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t148 : ((-31205067387/400000000000 : ℚ) : ℝ) ≤ stT237 148 := by
  have hc : ((-189813/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31205067387/400000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-189813/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c149 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-291231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186631/400000) (δ := 5979/500000000) (ψ := 69893/250000) 237 189
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t149 : ((-7457084881/312500000000 : ℚ) : ℝ) ≤ stT237 149 := by
  have hc : ((-291281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7457084881/312500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-291281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c150 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((960767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -351301/5000000) (δ := 5929/500000000) (ψ := 69893/250000) 237 189
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t150 : ((49026349227/625000000000 : ℚ) : ℝ) ≤ stT237 150 := by
  have hc : ((960717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49026349227/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((960717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c151 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((4274/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3234323/10000000) (δ := 2409/200000000) (ψ := 69893/250000) 237 189
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t151 : ((27819953121/1250000000000 : ℚ) : ℝ) ≤ stT237 151 := by
  have hc : ((136743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27819953121/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((136743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c152 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-960083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3572619/5000000) (δ := 2389/200000000) (ψ := 69893/250000) 237 189
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t152 : ((-194692889341/2500000000000 : ℚ) : ℝ) ≤ stT237 152 := by
  have hc : ((-960133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194692889341/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-960133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c153 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-147851/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2338733/5000000) (δ := 12037/1000000000) (ψ := 69893/250000) 237 190
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t153 : ((-29887698957/1250000000000 : ℚ) : ℝ) ≤ stT237 153 := by
  have hc : ((-36969/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29887698957/1250000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-36969/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c154 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((947009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -408753/5000000) (δ := 11937/1000000000) (ψ := 69893/250000) 237 190
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t154 : ((381540197649/5000000000000 : ℚ) : ℝ) ≤ stT237 154 := by
  have hc : ((946959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381540197649/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((946959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c155 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((355843/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60349/200000) (δ := 12037/1000000000) (ψ := 69893/250000) 237 190
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t155 : ((285779697667/10000000000000 : ℚ) : ℝ) ≤ stT237 155 := by
  have hc : ((355793/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285779697667/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((355793/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c156 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-458463/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6827759/10000000) (δ := 5983/500000000) (ψ := 69893/250000) 237 190
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t156 : ((-45885536351/625000000000 : ℚ) : ℝ) ≤ stT237 156 := by
  have hc : ((-57311/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45885536351/625000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-57311/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c157 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-450123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -636781/1250000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 191
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t157 : ((-359277219051/10000000000000 : ℚ) : ℝ) ≤ stT237 157 := by
  have hc : ((-450173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-359277219051/10000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-450173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c158 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((430659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1332347/10000000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 191
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t158 : ((171296946569/2500000000000 : ℚ) : ℝ) ≤ stT237 158 := by
  have hc : ((215317/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((171296946569/2500000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((215317/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c159 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((1429/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1202927/5000000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 191
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t159 : ((9065365981/200000000000 : ℚ) : ℝ) ≤ stT237 159 := by
  have hc : ((11431/20000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9065365981/200000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((11431/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c160 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-384553/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 382537/625000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 191
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t160 : ((-15201791473/250000000000 : ℚ) : ℝ) ≤ stT237 160 := by
  have hc : ((-192289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15201791473/250000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-192289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c161 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-11072/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29479/50000) (δ := 297/25000000) (ψ := 69893/250000) 237 192
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t161 : ((-279250582519/5000000000000 : ℚ) : ℝ) ≤ stT237 161 := by
  have hc : ((-354329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279250582519/5000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-354329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c162 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((314389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13919/62500) (δ := 297/25000000) (ψ := 69893/250000) 237 192
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t162 : ((30873452667/625000000000 : ℚ) : ℝ) ≤ stT237 162 := by
  have hc : ((78591/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30873452667/625000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((78591/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c163 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((421581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 709573/5000000) (δ := 599/50000000) (ψ := 69893/250000) 237 192
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t163 : ((4127349407/62500000000 : ℚ) : ℝ) ≤ stT237 163 := by
  have hc : ((105389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4127349407/62500000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((105389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c164 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-215861/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2521497/5000000) (δ := 11923/1000000000) (ψ := 69893/250000) 237 192
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t164 : ((-84289342467/2500000000000 : ℚ) : ℝ) ≤ stT237 164 := by
  have hc : ((-107943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84289342467/2500000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-107943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c165 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-59399/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3531581/5000000) (δ := 751/62500000) (ψ := 69893/250000) 237 193
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t165 : ((-369955959283/5000000000000 : ℚ) : ℝ) ≤ stT237 165 := by
  have hc : ((-475217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369955959283/5000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-475217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c166 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((1413/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3483099/10000000) (δ := 2979/250000000) (ψ := 69893/250000) 237 193
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t166 : ((109638949/8000000000 : ℚ) : ℝ) ≤ stT237 166 := by
  have hc : ((7063/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109638949/8000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((7063/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c167 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((124943/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15103/2000000) (δ := 751/62500000) (ψ := 69893/250000) 237 193
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t167 : ((386715722781/5000000000000 : ℚ) : ℝ) ≤ stT237 167 := by
  have hc : ((499747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((386715722781/5000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((499747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c168 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((62673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1129/3125) (δ := 11987/1000000000) (ψ := 69893/250000) 237 193
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t168 : ((1510435449/156250000000 : ℚ) : ℝ) ≤ stT237 168 := by
  have hc : ((7831/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).1
  have hw2 : ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((192879/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1510435449/156250000000 : ℚ) : ℝ)
      = ((192879/2500000 : ℚ) : ℝ) * ((7831/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c169 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-191653/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7129169/10000000) (δ := 11987/1000000000) (ψ := 69893/250000) 237 193
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t169 : ((-147433121153/2000000000000 : ℚ) : ℝ) ≤ stT237 169 := by
  have hc : ((-191663/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147433121153/2000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-191663/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c170 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-22309/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2541611/5000000) (δ := 5997/500000000) (ψ := 69893/250000) 237 194
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t170 : ((-6844855839/200000000000 : ℚ) : ℝ) ≤ stT237 170 := by
  have hc : ((-44623/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6844855839/200000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-44623/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c171 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((50009/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1608151/10000000) (δ := 12009/1000000000) (ψ := 69893/250000) 237 194
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t171 : ((305923541793/5000000000000 : ℚ) : ℝ) ≤ stT237 171 := by
  have hc : ((400047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305923541793/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((400047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c172 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((739369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 923329/5000000) (δ := 5997/500000000) (ψ := 69893/250000) 237 194
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t172 : ((140931205737/2500000000000 : ℚ) : ℝ) ≤ stT237 172 := by
  have hc : ((739319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140931205737/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((739319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c173 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-515661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5281439/10000000) (δ := 12009/1000000000) (ψ := 69893/250000) 237 194
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t173 : ((-196043926673/5000000000000 : ℚ) : ℝ) ≤ stT237 173 := by
  have hc : ((-515711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196043926673/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-515711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c174 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-471879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1752883/2500000) (δ := 12001/1000000000) (ψ := 69893/250000) 237 195
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t174 : ((-11179685953/156250000000 : ℚ) : ℝ) ≤ stT237 174 := by
  have hc : ((-14747/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11179685953/156250000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-14747/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c175 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((124039/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -904023/2500000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 195
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t175 : ((11715844599/1250000000000 : ℚ) : ℝ) ≤ stT237 175 := by
  have hc : ((123989/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11715844599/1250000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((123989/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c176 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((199079/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -240027/10000000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 195
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t176 : ((75026916341/1000000000000 : ℚ) : ℝ) ≤ stT237 176 := by
  have hc : ((199069/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((75026916341/1000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((199069/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c177 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((318373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19481/62500) (δ := 6001/500000000) (ψ := 69893/250000) 237 195
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t177 : ((119633104829/5000000000000 : ℚ) : ℝ) ≤ stT237 177 := by
  have hc : ((318323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119633104829/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((318323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c178 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-211867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3227493/5000000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 195
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t178 : ((-79405232697/1250000000000 : ℚ) : ℝ) ≤ stT237 178 := by
  have hc : ((-423759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79405232697/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-423759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c179 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-719199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2966807/5000000) (δ := 12009/1000000000) (ψ := 69893/250000) 237 196
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t179 : ((-134398148891/2500000000000 : ℚ) : ℝ) ≤ stT237 179 := by
  have hc : ((-719249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134398148891/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-719249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c180 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((494863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2632797/10000000) (δ := 5947/500000000) (ψ := 69893/250000) 237 196
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t180 : ((73762268723/2000000000000 : ℚ) : ℝ) ≤ stT237 180 := by
  have hc : ((494813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73762268723/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((494813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c181 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((966413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162443/2500000) (δ := 12009/1000000000) (ψ := 69893/250000) 237 196
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t181 : ((359145909861/5000000000000 : ℚ) : ℝ) ≤ stT237 181 := by
  have hc : ((966363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((359145909861/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((966363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c182 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((639/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391421/1000000) (δ := 12009/1000000000) (ψ := 69893/250000) 237 196
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t182 : ((1876101219/5000000000000 : ℚ) : ℝ) ≤ stT237 182 := by
  have hc : ((2531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1876101219/5000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((2531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c183 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-961807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7160813/10000000) (δ := 5997/500000000) (ψ := 69893/250000) 237 196
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t183 : ((-355512927627/5000000000000 : ℚ) : ℝ) ≤ stT237 183 := by
  have hc : ((-961857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355512927627/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-961857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c184 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-21129/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2659131/5000000) (δ := 11887/1000000000) (ψ := 69893/250000) 237 197
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t184 : ((-1557798451/40000000000 : ℚ) : ℝ) ≤ stT237 184 := by
  have hc : ((-21131/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1557798451/40000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-21131/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c185 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((665419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2106853/10000000) (δ := 11987/1000000000) (ψ := 69893/250000) 237 197
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t185 : ((244594301983/5000000000000 : ℚ) : ℝ) ≤ stT237 185 := by
  have hc : ((665369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244594301983/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((665369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c186 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((906921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 271799/2500000) (δ := 11987/1000000000) (ψ := 69893/250000) 237 197
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t186 : ((132989911537/2000000000000 : ℚ) : ℝ) ≤ stT237 186 := by
  have hc : ((906871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132989911537/2000000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((906871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c187 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-33617/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4264181/10000000) (δ := 11987/1000000000) (ψ := 69893/250000) 237 197
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t187 : ((-49184690707/5000000000000 : ℚ) : ℝ) ≤ stT237 187 := by
  have hc : ((-67259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49184690707/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-67259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c188 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-985257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3712081/5000000) (δ := 751/62500000) (ψ := 69893/250000) 237 197
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t188 : ((-28744361111/400000000000 : ℚ) : ℝ) ≤ stT237 188 := by
  have hc : ((-985307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28744361111/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-985307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c189 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-29161/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -514053/1000000) (δ := 297/25000000) (ψ := 69893/250000) 237 198
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t189 : ((-169710243009/5000000000000 : ℚ) : ℝ) ≤ stT237 189 := by
  have hc : ((-233313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169710243009/5000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-233313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c190 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((138541/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2013907/10000000) (δ := 12023/1000000000) (ψ := 69893/250000) 237 198
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t190 : ((25125228939/500000000000 : ℚ) : ℝ) ≤ stT237 190 := by
  have hc : ((138531/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25125228939/500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((138531/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c191 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((905371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548181/5000000) (δ := 297/25000000) (ψ := 69893/250000) 237 198
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t191 : ((327533368627/5000000000000 : ℚ) : ℝ) ≤ stT237 191 := by
  have hc : ((905321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327533368627/5000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((905321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c192 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-13143/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2095169/5000000) (δ := 11923/1000000000) (ψ := 69893/250000) 237 198
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t192 : ((-4744827967/625000000000 : ℚ) : ℝ) ≤ stT237 192 := by
  have hc : ((-52597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4744827967/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-52597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c193 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-972679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7268257/10000000) (δ := 11923/1000000000) (ψ := 69893/250000) 237 198
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t193 : ((-87523237233/1250000000000 : ℚ) : ℝ) ≤ stT237 193 := by
  have hc : ((-972729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87523237233/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-972729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c194 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-2193/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2688833/5000000) (δ := 1203/100000000) (ψ := 69893/250000) 237 199
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t194 : ((-3936569197/100000000000 : ℚ) : ℝ) ≤ stT237 194 := by
  have hc : ((-5483/10000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3936569197/100000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-5483/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c195 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((74473/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2331387/10000000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 199
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t195 : ((106653364419/2500000000000 : ℚ) : ℝ) ≤ stT237 195 := by
  have hc : ((297867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106653364419/2500000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((297867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c196 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((240283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69931/1000000) (δ := 1193/100000000) (ψ := 69893/250000) 237 199
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t196 : ((68648645637/1000000000000 : ℚ) : ℝ) ≤ stT237 196 := by
  have hc : ((480541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68648645637/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((480541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c197 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((84853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1857301/5000000) (δ := 1203/100000000) (ψ := 69893/250000) 237 199
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t197 : ((6041959341/1000000000000 : ℚ) : ℝ) ≤ stT237 197 := by
  have hc : ((84803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6041959341/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((84803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c198 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-897931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6714607/10000000) (δ := 1193/100000000) (ψ := 69893/250000) 237 199
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t198 : ((-63816815727/1000000000000 : ℚ) : ℝ) ≤ stT237 198 := by
  have hc : ((-897981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63816815727/1000000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-897981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c199 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-29587/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -300423/500000) (δ := 5933/500000000) (ψ := 69893/250000) 237 200
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t199 : ((-10487554749/200000000000 : ℚ) : ℝ) ≤ stT237 199 := by
  have hc : ((-29589/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10487554749/200000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-29589/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c200 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((173971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1519277/5000000) (δ := 5983/500000000) (ψ := 69893/250000) 237 200
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t200 : ((30749565069/1250000000000 : ℚ) : ℝ) ≤ stT237 200 := by
  have hc : ((86973/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30749565069/1250000000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((86973/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c201 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((249861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -83401/10000000) (δ := 5983/500000000) (ψ := 69893/250000) 237 200
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t201 : ((70491756093/1000000000000 : ℚ) : ℝ) ≤ stT237 201 := by
  have hc : ((499697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70491756093/1000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((499697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c202 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((415049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2856999/10000000) (δ := 5933/500000000) (ψ := 69893/250000) 237 200
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t202 : ((291992051403/10000000000000 : ℚ) : ℝ) ≤ stT237 202 := by
  have hc : ((414999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291992051403/10000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((414999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c203 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-169011/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2891471/5000000) (δ := 11937/1000000000) (ψ := 69893/250000) 237 200
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t203 : ((-237262681561/5000000000000 : ℚ) : ℝ) ≤ stT237 203 := by
  have hc : ((-338047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237262681561/5000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-338047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c204 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-472007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1753369/2500000) (δ := 2409/200000000) (ψ := 69893/250000) 237 201
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t204 : ((-10327779891/156250000000 : ℚ) : ℝ) ≤ stT237 204 := by
  have hc : ((-14751/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10327779891/156250000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-14751/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c205 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-9449/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4116151/10000000) (δ := 2409/200000000) (ψ := 69893/250000) 237 201
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t205 : ((-26415358851/5000000000000 : ℚ) : ℝ) ≤ stT237 205 := by
  have hc : ((-37821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26415358851/5000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-37821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c206 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((220209/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38529/312500) (δ := 5929/500000000) (ψ := 69893/250000) 237 201
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t206 : ((306836336069/5000000000000 : ℚ) : ℝ) ≤ stT237 206 := by
  have hc : ((440393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306836336069/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((440393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c207 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((793337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1636313/10000000) (δ := 2409/200000000) (ψ := 69893/250000) 237 201
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t207 : ((68921567847/1250000000000 : ℚ) : ℝ) ≤ stT237 207 := by
  have hc : ((793287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68921567847/1250000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((793287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c208 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-111993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1122937/2500000) (δ := 2389/200000000) (ψ := 69893/250000) 237 201
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t208 : ((-303400753/19531250000 : ℚ) : ℝ) ≤ stT237 208 := by
  have hc : ((-56009/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303400753/19531250000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-56009/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c209 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-489203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 916687/1250000) (δ := 5979/500000000) (ψ := 69893/250000) 237 201
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t209 : ((-16920317301/250000000000 : ℚ) : ℝ) ≤ stT237 209 := by
  have hc : ((-122307/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16920317301/250000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-122307/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c210 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-603369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5546287/10000000) (δ := 11951/1000000000) (ψ := 69893/250000) 237 202
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t210 : ((-208199467827/5000000000000 : ℚ) : ℝ) ≤ stT237 210 := by
  have hc : ((-603419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208199467827/5000000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-603419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c211 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((460159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -682889/2500000) (δ := 747/62500000) (ψ := 69893/250000) 237 202
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t211 : ((79187979663/2500000000000 : ℚ) : ℝ) ≤ stT237 211 := by
  have hc : ((460109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79187979663/2500000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((460109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c212 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((99961/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69843/10000000) (δ := 2963/250000000) (ψ := 69893/250000) 237 202
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t212 : ((8581247589/125000000000 : ℚ) : ℝ) ≤ stT237 212 := by
  have hc : ((24989/25000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8581247589/125000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((24989/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c213 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((103663/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2858089/10000000) (δ := 747/62500000) (ψ := 69893/250000) 237 202
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t213 : ((35510039397/1250000000000 : ℚ) : ℝ) ≤ stT237 213 := by
  have hc : ((207301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35510039397/1250000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((207301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c214 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-630753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5633299/10000000) (δ := 12051/1000000000) (ψ := 69893/250000) 237 202
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t214 : ((-215604049779/5000000000000 : ℚ) : ℝ) ≤ stT237 214 := by
  have hc : ((-630803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215604049779/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-630803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c215 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-976629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7312429/10000000) (δ := 1493/125000000) (ψ := 69893/250000) 237 203
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t215 : ((-133218038921/2000000000000 : ℚ) : ℝ) ≤ stT237 215 := by
  have hc : ((-976679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133218038921/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-976679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c216 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-50333/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -285187/625000) (δ := 1493/125000000) (ψ := 69893/250000) 237 203
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t216 : ((-17127041001/1000000000000 : ℚ) : ℝ) ≤ stT237 216 := by
  have hc : ((-50343/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17127041001/1000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-50343/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c217 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((744829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -913147/5000000) (δ := 3011/250000000) (ψ := 69893/250000) 237 203
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t217 : ((126397188869/2500000000000 : ℚ) : ℝ) ≤ stT237 217 := by
  have hc : ((744779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126397188869/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((744779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c218 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((4681/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224461/2500000) (δ := 11959/1000000000) (ψ := 69893/250000) 237 203
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t218 : ((2536161411/40000000000 : ℚ) : ℝ) ≤ stT237 218 := by
  have hc : ((18723/20000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2536161411/40000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((18723/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c219 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((1583/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1804769/5000000) (δ := 3011/250000000) (ψ := 69893/250000) 237 203
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t219 : ((8554154683/1000000000000 : ℚ) : ℝ) ≤ stT237 219 := by
  have hc : ((12659/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8554154683/1000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((12659/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c220 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-25469/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126177/200000) (δ := 11859/1000000000) (ψ := 69893/250000) 237 203
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t220 : ((-1373780259/25000000000 : ℚ) : ℝ) ≤ stT237 220 := by
  have hc : ((-407529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1373780259/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-407529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c221 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-897473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6712007/10000000) (δ := 5983/500000000) (ψ := 69893/250000) 237 204
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t221 : ((-603739488979/10000000000000 : ℚ) : ℝ) ≤ stT237 221 := by
  have hc : ((-897523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-603739488979/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-897523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c222 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-688/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4037107/10000000) (δ := 11937/1000000000) (ψ := 69893/250000) 237 204
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t222 : ((-14792971437/5000000000000 : ℚ) : ℝ) ≤ stT237 222 := by
  have hc : ((-22041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14792971437/5000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-22041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c223 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((852697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54967/400000) (δ := 11937/1000000000) (ψ := 69893/250000) 237 204
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t223 : ((570974210903/10000000000000 : ℚ) : ℝ) ≤ stT237 223 := by
  have hc : ((852647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((570974210903/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((852647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c224 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((872383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79803/625000) (δ := 5933/500000000) (ψ := 69893/250000) 237 204
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t224 : ((582851910949/10000000000000 : ℚ) : ℝ) ≤ stT237 224 := by
  have hc : ((872333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((582851910949/10000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((872333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c225 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((1091/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48951/125000) (δ := 5933/500000000) (ψ := 69893/250000) 237 204
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t225 : ((718999281/2500000000000 : ℚ) : ℝ) ≤ stT237 225 := by
  have hc : ((2157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718999281/2500000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((2157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c226 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-865739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6543551/10000000) (δ := 11883/500000000) (ψ := 69893/250000) 237 204
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t226 : ((-575915050699/10000000000000 : ℚ) : ℝ) ≤ stT237 226 := by
  have hc : ((-865789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575915050699/10000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-865789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c227 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-866727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1309699/2000000) (δ := 11973/1000000000) (ψ := 69893/250000) 237 205
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t227 : ((-143825174387/2500000000000 : ℚ) : ℝ) ≤ stT237 227 := by
  have hc : ((-866777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143825174387/2500000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-866777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c228 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-1711/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1972051/5000000) (δ := 11973/1000000000) (ψ := 69893/250000) 237 205
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t228 : ((-2282834349/5000000000000 : ℚ) : ℝ) ≤ stT237 228 := by
  have hc : ((-3447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2282834349/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-3447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c229 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((171497/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270217/2000000) (δ := 11973/1000000000) (ψ := 69893/250000) 237 205
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t229 : ((56660848183/1000000000000 : ℚ) : ℝ) ≤ stT237 229 := by
  have hc : ((171487/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56660848183/1000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((171487/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c230 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((440637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 246123/2000000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 205
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t230 : ((3631634257/62500000000 : ℚ) : ℝ) ≤ stT237 230 := by
  have hc : ((110153/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3631634257/62500000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((110153/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c231 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((6291/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3801117/10000000) (δ := 11873/1000000000) (ψ := 69893/250000) 237 205
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t231 : ((16540230189/5000000000000 : ℚ) : ℝ) ≤ stT237 231 := by
  have hc : ((25139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16540230189/5000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((25139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c232 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-826801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39753/62500) (δ := 11873/1000000000) (ψ := 69893/250000) 237 205
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t232 : ((-542854967583/10000000000000 : ℚ) : ℝ) ≤ stT237 232 := by
  have hc : ((-826851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-542854967583/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-826851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c233 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-28509/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3399541/5000000) (δ := 12023/1000000000) (ψ := 69893/250000) 237 206
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t233 : ((-149423173809/2500000000000 : ℚ) : ℝ) ≤ stT237 233 := by
  have hc : ((-456169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149423173809/2500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-456169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c234 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-133437/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2130791/5000000) (δ := 11923/1000000000) (ψ := 69893/250000) 237 206
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t234 : ((-87263255127/10000000000000 : ℚ) : ℝ) ≤ stT237 234 := by
  have hc : ((-133487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87263255127/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-133487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c235 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((768713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69397/400000) (δ := 11923/1000000000) (ψ := 69893/250000) 237 206
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t235 : ((62677549683/1250000000000 : ℚ) : ℝ) ≤ stT237 235 := by
  have hc : ((768663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62677549683/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((768663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c236 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((475799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48813/625000) (δ := 297/25000000) (ψ := 69893/250000) 237 206
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t236 : ((2419548677/39062500000 : ℚ) : ℝ) ≤ stT237 236 := by
  have hc : ((237887/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2419548677/39062500000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((237887/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c237 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((25349/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 821569/2500000) (δ := 599/50000000) (ψ := 69893/250000) 237 206
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t237 : ((64307331/3906250000 : ℚ) : ℝ) ≤ stT237 237 := by
  have hc : ((792/3125 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64307331/3906250000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((792/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c238 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-67547/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5780997/10000000) (δ := 297/25000000) (ψ := 69893/250000) 237 206
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t238 : ((-342089661/7812500000 : ℚ) : ℝ) ≤ stT237 238 := by
  have hc : ((-2111/3125 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342089661/7812500000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-2111/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c239 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-986497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7442673/10000000) (δ := 743/62500000) (ψ := 69893/250000) 237 207
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t239 : ((-638144967309/10000000000000 : ℚ) : ℝ) ≤ stT237 239 := by
  have hc : ((-986547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-638144967309/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-986547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c240 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-101187/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4968749/10000000) (δ := 2403/200000000) (ψ := 69893/250000) 237 207
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t240 : ((-65324074851/2500000000000 : ℚ) : ℝ) ≤ stT237 240 := by
  have hc : ((-202399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65324074851/2500000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-202399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c241 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((538573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1252567/5000000) (δ := 2403/200000000) (ψ := 69893/250000) 237 207
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t241 : ((86723205397/2500000000000 : ℚ) : ℝ) ≤ stT237 241 := by
  have hc : ((538523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86723205397/2500000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((538523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c242 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((499893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5171/1000000) (δ := 2403/200000000) (ψ := 69893/250000) 237 207
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t242 : ((10041473351/156250000000 : ℚ) : ℝ) ≤ stT237 242 := by
  have hc : ((124967/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10041473351/156250000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((124967/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c243 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((23051/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2391583/10000000) (δ := 2997/250000000) (ψ := 69893/250000) 237 207
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t243 : ((29571867/800000000 : ℚ) : ℝ) ≤ stT237 243 := by
  have hc : ((23049/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29571867/800000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((23049/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c244 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-351477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2412431/5000000) (δ := 2997/250000000) (ψ := 69893/250000) 237 207
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t244 : ((-45008462499/2000000000000 : ℚ) : ℝ) ≤ stT237 244 := by
  have hc : ((-351527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45008462499/2000000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-351527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c245 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-485391/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7248157/10000000) (δ := 4743/200000000) (ψ := 69893/250000) 237 207
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t245 : ((-38765139729/625000000000 : ℚ) : ℝ) ≤ stT237 245 := by
  have hc : ((-60677/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38765139729/625000000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-60677/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c246 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-187447/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3023173/5000000) (δ := 2399/200000000) (ψ := 69893/250000) 237 208
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t246 : ((-239039731263/5000000000000 : ℚ) : ℝ) ≤ stT237 246 := by
  have hc : ((-374919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239039731263/5000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-374919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c247 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((4539/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -910673/2500000) (δ := 2399/200000000) (ψ := 69893/250000) 237 208
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t247 : ((721705127/100000000000 : ℚ) : ℝ) ≤ stT237 247 := by
  have hc : ((4537/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((721705127/100000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((4537/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c248 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((877821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -249751/2000000) (δ := 2399/200000000) (ψ := 69893/250000) 237 208
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t248 : ((111476917/2000000000 : ℚ) : ℝ) ≤ stT237 248 := by
  have hc : ((877771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111476917/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((877771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c249 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((56163/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 283881/2500000) (δ := 2379/200000000) (ψ := 69893/250000) 237 208
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t249 : ((71179721249/1250000000000 : ℚ) : ℝ) ≤ stT237 249 := by
  have hc : ((449279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71179721249/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((449279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c250 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((165897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3510323/10000000) (δ := 2977/250000000) (ψ := 69893/250000) 237 208
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t250 : ((20978152877/2000000000000 : ℚ) : ℝ) ≤ stT237 250 := by
  have hc : ((165847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20978152877/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((165847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c251 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-702879/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5875583/10000000) (δ := 2977/250000000) (ψ := 69893/250000) 237 208
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t251 : ((-88737054031/2000000000000 : ℚ) : ℝ) ≤ stT237 251 := by
  have hc : ((-702929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).2
  have h0 : (0:ℝ) ≤ ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88737054031/2000000000000 : ℚ) : ℝ)
      = ((126239/2000000 : ℚ) : ℝ) * ((-702929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c252 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-7909/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7476541/10000000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 209
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t252 : ((-24912276727/400000000000 : ℚ) : ℝ) ≤ stT237 252 := by
  have hc : ((-39547/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24912276727/400000000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-39547/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c253 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-7232/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1282501/2500000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 209
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t253 : ((-29102165811/1000000000000 : ℚ) : ℝ) ≤ stT237 253 := by
  have hc : ((-231449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29102165811/1000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-231449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c254 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((87661/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -279271/1000000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 209
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t254 : ((10999411641/400000000000 : ℚ) : ℝ) ≤ stT237 254 := by
  have hc : ((87651/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).1
  have hw2 : ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((125491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10999411641/400000000000 : ℚ) : ℝ)
      = ((125491/2000000 : ℚ) : ℝ) * ((87651/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c255 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((982781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2323/50000) (δ := 12001/1000000000) (ψ := 69893/250000) 237 209
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t255 : ((38463108609/625000000000 : ℚ) : ℝ) ≤ stT237 255 := by
  have hc : ((982731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38463108609/625000000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((982731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c256 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((184321/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 927193/5000000) (δ := 11901/1000000000) (ψ := 69893/250000) 237 209
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t256 : ((368617/8000000 : ℚ) : ℝ) ≤ stT237 256 := by
  have hc : ((368617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((368617/8000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((368617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c257 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-1481/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4164307/10000000) (δ := 6001/500000000) (ψ := 69893/250000) 237 209
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t257 : ((-29577918511/5000000000000 : ℚ) : ℝ) ≤ stT237 257 := by
  have hc : ((-47417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29577918511/5000000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-47417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c258 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-849647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 10102/15625) (δ := 12001/1000000000) (ψ := 69893/250000) 237 209
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t258 : ((-528998410381/10000000000000 : ℚ) : ℝ) ≤ stT237 258 := by
  have hc : ((-849697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528998410381/10000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-849697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c259 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-935419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6950597/10000000) (δ := 5997/500000000) (ψ := 69893/250000) 237 210
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t259 : ((-58127237253/1000000000000 : ℚ) : ℝ) ≤ stT237 259 := by
  have hc : ((-935469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58127237253/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-935469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c260 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-29183/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4667339/10000000) (δ := 5997/500000000) (ψ := 69893/250000) 237 210
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t260 : ((-2262704839/125000000000 : ℚ) : ℝ) ≤ stT237 260 := by
  have hc : ((-7297/25000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2262704839/125000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-7297/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c261 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((575861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47857/200000) (δ := 5997/500000000) (ψ := 69893/250000) 237 210
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t261 : ((44552224503/1250000000000 : ℚ) : ℝ) ≤ stT237 261 := by
  have hc : ((575811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44552224503/1250000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((575811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c262 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((998709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12707/1000000) (δ := 35709/1000000000) (ψ := 69893/250000) 237 210
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t262 : ((308486763759/5000000000000 : ℚ) : ℝ) ≤ stT237 262 := by
  have hc : ((998659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308486763759/5000000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((998659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c263 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((329231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1065029/5000000) (δ := 5997/500000000) (ψ := 69893/250000) 237 210
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t263 : ((50749244739/1250000000000 : ℚ) : ℝ) ≤ stT237 263 := by
  have hc : ((164603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50749244739/1250000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((164603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c264 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-44921/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 875731/2000000) (δ := 17797/500000000) (ψ := 69893/250000) 237 210
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t264 : ((-27654682043/2500000000000 : ℚ) : ℝ) ≤ stT237 264 := by
  have hc : ((-89867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27654682043/2500000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-89867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c265 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-440197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41367/62500) (δ := 11909/1000000000) (ψ := 69893/250000) 237 210
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t265 : ((-16901663357/312500000000 : ℚ) : ℝ) ≤ stT237 265 := by
  have hc : ((-220111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).2
  have h0 : (0:ℝ) ≤ ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16901663357/312500000000 : ℚ) : ℝ)
      = ((76787/1250000 : ℚ) : ℝ) * ((-220111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c266 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-460811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -857199/1250000) (δ := 2979/250000000) (ψ := 69893/250000) 237 211
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t266 : ((-3531962313/62500000000 : ℚ) : ℝ) ≤ stT237 266 := by
  have hc : ((-115209/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).2
  have h0 : (0:ℝ) ≤ ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3531962313/62500000000 : ℚ) : ℝ)
      = ((30657/500000 : ℚ) : ℝ) * ((-115209/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c267 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-55837/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2317177/5000000) (δ := 751/62500000) (ψ := 69893/250000) 237 211
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t267 : ((-34177861377/2000000000000 : ℚ) : ℝ) ≤ stT237 267 := by
  have hc : ((-55847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34177861377/2000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-55847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c268 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((283571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604853/2500000) (δ := 11987/1000000000) (ψ := 69893/250000) 237 211
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t268 : ((86601611731/2500000000000 : ℚ) : ℝ) ≤ stT237 268 := by
  have hc : ((141773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).1
  have hw2 : ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86601611731/2500000000000 : ℚ) : ℝ)
      = ((610847/10000000 : ℚ) : ℝ) * ((141773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c269 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((996383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42541/2000000) (δ := 11987/1000000000) (ψ := 69893/250000) 237 211
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t269 : ((60747419343/1000000000000 : ℚ) : ℝ) ≤ stT237 269 := by
  have hc : ((996333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).1
  have hw2 : ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60971/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60747419343/1000000000000 : ℚ) : ℝ)
      = ((60971/1000000 : ℚ) : ℝ) * ((996333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c270 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((700763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 992913/5000000) (δ := 2979/250000000) (ψ := 69893/250000) 237 211
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t270 : ((21321995877/500000000000 : ℚ) : ℝ) ≤ stT237 270 := by
  have hc : ((700713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21321995877/500000000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((700713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c271 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-49767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4176239/10000000) (δ := 11887/1000000000) (ψ := 69893/250000) 237 211
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t271 : ((-236300773/39062500000 : ℚ) : ℝ) ≤ stT237 271 := by
  have hc : ((-1556/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).2
  have h0 : (0:ℝ) ≤ ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236300773/39062500000 : ℚ) : ℝ)
      = ((607457/10000000 : ℚ) : ℝ) * ((-1556/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c272 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-826363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1271707/2000000) (δ := 11887/1000000000) (ψ := 69893/250000) 237 211
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t272 : ((-25054362921/500000000000 : ℚ) : ℝ) ≤ stT237 272 := by
  have hc : ((-826413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).2
  have h0 : (0:ℝ) ≤ ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25054362921/500000000000 : ℚ) : ℝ)
      = ((30317/500000 : ℚ) : ℝ) * ((-826413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c273 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-963359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7175131/10000000) (δ := 11879/1000000000) (ψ := 69893/250000) 237 212
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t273 : ((-145770525563/2500000000000 : ℚ) : ℝ) ≤ stT237 273 := by
  have hc : ((-963409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145770525563/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-963409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c274 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-209657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2504357/5000000) (δ := 11879/1000000000) (ψ := 69893/250000) 237 212
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t274 : ((-63336859443/2500000000000 : ℚ) : ℝ) ≤ stT237 274 := by
  have hc : ((-104841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63336859443/2500000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-104841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c275 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((417487/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -356287/1250000) (δ := 11979/1000000000) (ψ := 69893/250000) 237 212
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t275 : ((125861847307/5000000000000 : ℚ) : ℝ) ≤ stT237 275 := by
  have hc : ((417437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).1
  have hw2 : ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((301511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125861847307/5000000000000 : ℚ) : ℝ)
      = ((301511/5000000 : ℚ) : ℝ) * ((417437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c276 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((192219/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -699639/10000000) (δ := 2981/250000000) (ψ := 69893/250000) 237 212
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t276 : ((115696171161/2000000000000 : ℚ) : ℝ) ≤ stT237 276 := by
  have hc : ((192209/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115696171161/2000000000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((192209/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c277 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((418969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180407/1250000) (δ := 1503/125000000) (ψ := 69893/250000) 237 212
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t277 : ((1966552593/39062500000 : ℚ) : ℝ) ≤ stT237 277 := by
  have hc : ((13092/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1966552593/39062500000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((13092/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c278 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((138989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3578389/10000000) (δ := 1503/125000000) (ψ := 69893/250000) 237 212
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t278 : ((1041625683/125000000000 : ℚ) : ℝ) ≤ stT237 278 := by
  have hc : ((138939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).1
  have hw2 : ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7497/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1041625683/125000000000 : ℚ) : ℝ)
      = ((7497/125000 : ℚ) : ℝ) * ((138939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c279 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-326497/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5705819/10000000) (δ := 11879/1000000000) (ψ := 69893/250000) 237 212
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t279 : ((-19548382357/500000000000 : ℚ) : ℝ) ≤ stT237 279 := by
  have hc : ((-163261/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19548382357/500000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-163261/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c280 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-15624/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 313029/400000) (δ := 2981/250000000) (ψ := 69893/250000) 237 212
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t280 : ((-59760663339/1000000000000 : ℚ) : ℝ) ≤ stT237 280 := by
  have hc : ((-499993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59760663339/1000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-499993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c281 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-672213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -721247/1250000) (δ := 371/31250000) (ψ := 69893/250000) 237 213
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t281 : ((-8020769853/200000000000 : ℚ) : ℝ) ≤ stT237 281 := by
  have hc : ((-672263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).2
  have h0 : (0:ℝ) ≤ ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8020769853/200000000000 : ℚ) : ℝ)
      = ((11931/200000 : ℚ) : ℝ) * ((-672263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c282 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((104533/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3665179/10000000) (δ := 371/31250000) (ψ := 69893/250000) 237 213
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t282 : ((62218686153/10000000000000 : ℚ) : ℝ) ≤ stT237 282 := by
  have hc : ((104483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62218686153/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((104483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c283 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((80971/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1567847/10000000) (δ := 12031/1000000000) (ψ := 69893/250000) 237 213
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t283 : ((12032316777/250000000000 : ℚ) : ℝ) ≤ stT237 283 := by
  have hc : ((40483/50000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12032316777/250000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((40483/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c284 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((978269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 522137/10000000) (δ := 371/31250000) (ψ := 69893/250000) 237 213
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t284 : ((58046537241/1000000000000 : ℚ) : ℝ) ≤ stT237 284 := by
  have hc : ((978219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).1
  have hw2 : ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((59339/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58046537241/1000000000000 : ℚ) : ℝ)
      = ((59339/1000000 : ℚ) : ℝ) * ((978219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c285 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((504593/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 520943/2000000) (δ := 2993/250000000) (ψ := 69893/250000) 237 213
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t285 : ((74716259241/2500000000000 : ℚ) : ℝ) ≤ stT237 285 := by
  have hc : ((504543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).1
  have hw2 : ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((148087/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74716259241/2500000000000 : ℚ) : ℝ)
      = ((148087/2500000 : ℚ) : ℝ) * ((504543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c286 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-59339/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 936013/2000000) (δ := 371/31250000) (ψ := 69893/250000) 237 213
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t286 : ((-35093835237/2000000000000 : ℚ) : ℝ) ≤ stT237 286 := by
  have hc : ((-59349/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35093835237/2000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-59349/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c287 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-112969/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6748127/10000000) (δ := 371/31250000) (ψ := 69893/250000) 237 213
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t287 : ((-133374513041/2500000000000 : ℚ) : ℝ) ≤ stT237 287 := by
  have hc : ((-451901/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).2
  have h0 : (0:ℝ) ≤ ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133374513041/2500000000000 : ℚ) : ℝ)
      = ((295141/5000000 : ℚ) : ℝ) * ((-451901/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c288 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-231981/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6899003/10000000) (δ := 2393/200000000) (ψ := 69893/250000) 237 214
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t288 : ((-34175890459/625000000000 : ℚ) : ℝ) ≤ stT237 288 := by
  have hc : ((-463987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).2
  have h0 : (0:ℝ) ≤ ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34175890459/625000000000 : ℚ) : ℝ)
      = ((73657/1250000 : ℚ) : ℝ) * ((-463987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c289 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-359111/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4845279/10000000) (δ := 5969/500000000) (ψ := 69893/250000) 237 214
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t289 : ((-52817857499/2500000000000 : ℚ) : ℝ) ≤ stT237 289 := by
  have hc : ((-359161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52817857499/2500000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-359161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c290 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((54523/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1399303/5000000) (δ := 6019/500000000) (ψ := 69893/250000) 237 214
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t290 : ((6402665187/250000000000 : ℚ) : ℝ) ≤ stT237 290 := by
  have hc : ((218067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6402665187/250000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((218067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c291 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((954261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -189761/2500000) (δ := 2393/200000000) (ψ := 69893/250000) 237 214
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t291 : ((55936803031/1000000000000 : ℚ) : ℝ) ≤ stT237 291 := by
  have hc : ((954211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55936803031/1000000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((954211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c292 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((43651/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1273587/10000000) (δ := 5969/500000000) (ψ := 69893/250000) 237 214
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t292 : ((10217328177/200000000000 : ℚ) : ℝ) ≤ stT237 292 := by
  have hc : ((87297/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10217328177/200000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((87297/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c293 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((9939/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1649613/5000000) (δ := 5969/500000000) (ψ := 69893/250000) 237 214
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t293 : ((2902627511/200000000000 : ℚ) : ℝ) ≤ stT237 293 := by
  have hc : ((9937/40000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2902627511/200000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((9937/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c294 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-528113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5317933/10000000) (δ := 6019/500000000) (ψ := 69893/250000) 237 214
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t294 : ((-77007749889/2500000000000 : ℚ) : ℝ) ≤ stT237 294 := by
  have hc : ((-528163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77007749889/2500000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-528163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c295 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-978101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3664913/5000000) (δ := 6019/500000000) (ψ := 69893/250000) 237 214
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t295 : ((-569502009673/10000000000000 : ℚ) : ℝ) ≤ stT237 295 := by
  have hc : ((-978151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-569502009673/10000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-978151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c296 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-41481/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3186529/5000000) (δ := 2409/200000000) (ψ := 69893/250000) 237 215
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t296 : ((-48223656113/1000000000000 : ℚ) : ℝ) ≤ stT237 296 := by
  have hc : ((-82967/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48223656113/1000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-82967/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c297 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-178141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2187367/5000000) (δ := 5979/500000000) (ψ := 69893/250000) 237 215
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t297 : ((-103396931469/10000000000000 : ℚ) : ℝ) ≤ stT237 297 := by
  have hc : ((-178191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103396931469/10000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-178191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c298 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((36189/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2383163/10000000) (δ := 2409/200000000) (ψ := 69893/250000) 237 215
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t298 : ((41923796827/1250000000000 : ℚ) : ℝ) ≤ stT237 298 := by
  have hc : ((289487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41923796827/1250000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((289487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c299 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((49367/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -398229/10000000) (δ := 2389/200000000) (ψ := 69893/250000) 237 215
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t299 : ((28548181453/500000000000 : ℚ) : ℝ) ≤ stT237 299 := by
  have hc : ((98729/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28548181453/500000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((98729/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c300 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((806831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1580069/10000000) (δ := 5929/500000000) (ψ := 69893/250000) 237 215
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t300 : ((9315900207/200000000000 : ℚ) : ℝ) ≤ stT237 300 := by
  have hc : ((806781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9315900207/200000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((806781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c301 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((149517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3551791/10000000) (δ := 2409/200000000) (ψ := 69893/250000) 237 215
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t301 : ((8615128413/1000000000000 : ℚ) : ℝ) ≤ stT237 301 := by
  have hc : ((149467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).1
  have hw2 : ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57639/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8615128413/1000000000000 : ℚ) : ℝ)
      = ((57639/1000000 : ℚ) : ℝ) * ((149467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c302 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-9281/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1103399/2000000) (δ := 2409/200000000) (ψ := 69893/250000) 237 215
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t302 : ((-42728568603/1250000000000 : ℚ) : ℝ) ≤ stT237 302 := by
  have hc : ((-297017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42728568603/1250000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-297017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c303 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-988573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7475681/10000000) (δ := 5929/500000000) (ψ := 69893/250000) 237 215
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t303 : ((-113589816831/2000000000000 : ℚ) : ℝ) ≤ stT237 303 := by
  have hc : ((-988623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113589816831/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-988623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c304 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-20207/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3140027/5000000) (δ := 2963/250000000) (ψ := 69893/250000) 237 216
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t304 : ((-2318047941/50000000000 : ℚ) : ℝ) ≤ stT237 304 := by
  have hc : ((-80833/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2318047941/50000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-80833/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c305 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-81099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1083571/2500000) (δ := 2963/250000000) (ψ := 69893/250000) 237 216
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t305 : ((-11612880319/1250000000000 : ℚ) : ℝ) ≤ stT237 305 := by
  have hc : ((-20281/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).2
  have h0 : (0:ℝ) ≤ ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11612880319/1250000000000 : ℚ) : ℝ)
      = ((572599/10000000 : ℚ) : ℝ) * ((-20281/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c306 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((71903/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -478959/2000000) (δ := 12051/1000000000) (ψ := 69893/250000) 237 216
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t306 : ((164402272007/5000000000000 : ℚ) : ℝ) ≤ stT237 306 := by
  have hc : ((287587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164402272007/5000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((287587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c307 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((196599/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57713/1250000) (δ := 2963/250000000) (ψ := 69893/250000) 237 216
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t307 : ((11219923997/200000000000 : ℚ) : ℝ) ≤ stT237 307 := by
  have hc : ((196589/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11219923997/200000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((196589/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c308 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((52071/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 732553/5000000) (δ := 2963/250000000) (ψ := 69893/250000) 237 216
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t308 : ((118673517243/2500000000000 : ℚ) : ℝ) ≤ stT237 308 := by
  have hc : ((416543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118673517243/2500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((416543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c309 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((214831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 677139/2000000) (δ := 747/62500000) (ψ := 69893/250000) 237 216
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t309 : ((1527307691/125000000000 : ℚ) : ℝ) ≤ stT237 309 := by
  have hc : ((214781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).1
  have hw2 : ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7111/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1527307691/125000000000 : ℚ) : ℝ)
      = ((7111/125000 : ℚ) : ℝ) * ((214781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c310 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-522029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2650031/5000000) (δ := 11951/1000000000) (ψ := 69893/250000) 237 216
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t310 : ((-148260516499/5000000000000 : ℚ) : ℝ) ≤ stT237 310 := by
  have hc : ((-522079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148260516499/5000000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-522079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c311 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-193367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7208327/10000000) (δ := 2963/250000000) (ψ := 69893/250000) 237 216
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t311 : ((-13706755137/250000000000 : ℚ) : ℝ) ≤ stT237 311 := by
  have hc : ((-193377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13706755137/250000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-193377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c312 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-175271/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6597593/10000000) (δ := 1493/125000000) (ψ := 69893/250000) 237 217
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t312 : ((-99233410059/2000000000000 : ℚ) : ℝ) ≤ stT237 312 := by
  have hc : ((-175281/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99233410059/2000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-175281/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c313 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-304907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4701593/10000000) (δ := 1493/125000000) (ψ := 69893/250000) 237 217
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t313 : ((-86186032469/5000000000000 : ℚ) : ℝ) ≤ stT237 313 := by
  have hc : ((-304957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86186032469/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-304957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c314 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((6742/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -702909/2500000) (δ := 11959/1000000000) (ψ := 69893/250000) 237 217
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t314 : ((30434283677/1250000000000 : ℚ) : ℝ) ≤ stT237 314 := by
  have hc : ((215719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30434283677/1250000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((215719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c315 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((931941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -57979/625000) (δ := 11859/1000000000) (ψ := 69893/250000) 237 217
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t315 : ((131265234369/2500000000000 : ℚ) : ℝ) ≤ stT237 315 := by
  have hc : ((931891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131265234369/2500000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((931891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c316 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((928617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237581/2500000) (δ := 11859/1000000000) (ψ := 69893/250000) 237 217
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t316 : ((522358865881/10000000000000 : ℚ) : ℝ) ≤ stT237 316 := by
  have hc : ((928567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((522358865881/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((928567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c317 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((213813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 352791/1250000) (δ := 11959/1000000000) (ψ := 69893/250000) 237 217
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t317 : ((6003754957/250000000000 : ℚ) : ℝ) ≤ stT237 317 := by
  have hc : ((53447/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6003754957/250000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((53447/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c318 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-149951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2344233/5000000) (δ := 11959/1000000000) (ψ := 69893/250000) 237 217
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t318 : ((-10512811431/625000000000 : ℚ) : ℝ) ≤ stT237 318 := by
  have hc : ((-18747/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10512811431/625000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-18747/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c319 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-866787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6548797/10000000) (δ := 1493/125000000) (ψ := 69893/250000) 237 217
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t319 : ((-485335968441/10000000000000 : ℚ) : ℝ) ≤ stT237 319 := by
  have hc : ((-866837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485335968441/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-866837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c320 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-195193/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -182619/250000) (δ := 3009/250000000) (ψ := 69893/250000) 237 218
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t320 : ((-109121795451/2000000000000 : ℚ) : ℝ) ≤ stT237 320 := by
  have hc : ((-195203/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109121795451/2000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-195203/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c321 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-114839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5456041/10000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 218
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t321 : ((-32051254977/1000000000000 : ℚ) : ℝ) ≤ stT237 321 := by
  have hc : ((-114849/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32051254977/1000000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-114849/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c322 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((25043/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3613129/10000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 218
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t322 : ((6975170087/1000000000000 : ℚ) : ℝ) ≤ stT237 322 := by
  have hc : ((25033/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6975170087/1000000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((25033/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c323 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((379063/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -355181/2000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 218
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t323 : ((52725512433/1250000000000 : ℚ) : ℝ) ≤ stT237 323 := by
  have hc : ((189519/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52725512433/1250000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((189519/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c324 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((124969/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 55631/10000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 218
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t324 : ((55538944461/1000000000000 : ℚ) : ℝ) ≤ stT237 324 := by
  have hc : ((499851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55538944461/1000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((499851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c325 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((2281/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1881479/10000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 218
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t325 : ((404858889/10000000000 : ℚ) : ℝ) ≤ stT237 325 := by
  have hc : ((72987/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((404858889/10000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((72987/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c326 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((22493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3701757/10000000) (δ := 3009/250000000) (ψ := 69893/250000) 237 218
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t326 : ((3112694991/625000000000 : ℚ) : ℝ) ≤ stT237 326 := by
  have hc : ((44961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3112694991/625000000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((44961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c327 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-593813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2758233/5000000) (δ := 3009/250000000) (ψ := 69893/250000) 237 218
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t327 : ((-164203713363/5000000000000 : ℚ) : ℝ) ≤ stT237 327 := by
  have hc : ((-593863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164203713363/5000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-593863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c328 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-488877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1465133/2000000) (δ := 373/31250000) (ψ := 69893/250000) 237 218
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t328 : ((-67487787629/1250000000000 : ℚ) : ℝ) ≤ stT237 328 := by
  have hc : ((-244451/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67487787629/1250000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-244451/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c329 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-872683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6578669/10000000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 219
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t329 : ((-240576706047/5000000000000 : ℚ) : ℝ) ≤ stT237 329 := by
  have hc : ((-872733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240576706047/5000000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-872733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c330 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-334807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4780491/10000000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 219
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t330 : ((-92166375537/5000000000000 : ℚ) : ℝ) ≤ stT237 330 := by
  have hc : ((-334857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92166375537/5000000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-334857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c331 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((91729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2987763/10000000) (δ := 5987/500000000) (ψ := 69893/250000) 237 219
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t331 : ((100823765017/5000000000000 : ℚ) : ℝ) ≤ stT237 331 := by
  have hc : ((183433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).1
  have hw2 : ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((549649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((100823765017/5000000000000 : ℚ) : ℝ)
      = ((549649/10000000 : ℚ) : ℝ) * ((183433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c332 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((221729/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -300107/2500000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 219
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t332 : ((243365342493/5000000000000 : ℚ) : ℝ) ≤ stT237 332 := by
  have hc : ((443433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).1
  have hw2 : ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((243365342493/5000000000000 : ℚ) : ℝ)
      = ((548821/10000000 : ℚ) : ℝ) * ((443433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c333 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((973069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145379/2500000) (δ := 5937/500000000) (ψ := 69893/250000) 237 219
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t333 : ((133302629981/2500000000000 : ℚ) : ℝ) ≤ stT237 333 := by
  have hc : ((973019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133302629981/2500000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((973019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c334 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((14679/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2358127/10000000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 219
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t334 : ((1285007657/40000000000 : ℚ) : ℝ) ≤ stT237 334 := by
  have hc : ((58711/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1285007657/40000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((58711/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c335 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-80901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 825893/2000000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 219
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t335 : ((-44228307409/10000000000000 : ℚ) : ℝ) ≤ stT237 335 := by
  have hc : ((-80951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).2
  have h0 : (0:ℝ) ≤ ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44228307409/10000000000000 : ℚ) : ℝ)
      = ((546359/10000000 : ℚ) : ℝ) * ((-80951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c336 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-141703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5895471/10000000) (δ := 5987/500000000) (ψ := 69893/250000) 237 219
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t336 : ((-15462163717/400000000000 : ℚ) : ℝ) ≤ stT237 336 := by
  have hc : ((-141713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).2
  have h0 : (0:ℝ) ≤ ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15462163717/400000000000 : ℚ) : ℝ)
      = ((109109/2000000 : ℚ) : ℝ) * ((-141713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c337 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-498437/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3828131/5000000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 219
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t337 : ((-27152969757/500000000000 : ℚ) : ℝ) ≤ stT237 337 := by
  have hc : ((-249231/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).2
  have h0 : (0:ℝ) ≤ ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27152969757/500000000000 : ℚ) : ℝ)
      = ((108947/2000000 : ℚ) : ℝ) * ((-249231/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c338 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-406031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6296183/10000000) (δ := 5961/500000000) (ψ := 69893/250000) 237 220
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t338 : ((-27608204253/625000000000 : ℚ) : ℝ) ≤ stT237 338 := by
  have hc : ((-50757/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27608204253/625000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-50757/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c339 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-61247/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28411/62500) (δ := 11881/1000000000) (ψ := 69893/250000) 237 220
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t339 : ((-33271627197/2500000000000 : ℚ) : ℝ) ≤ stT237 339 := by
  have hc : ((-122519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33271627197/2500000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-122519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c340 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((108871/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2800551/10000000) (δ := 11981/1000000000) (ψ := 69893/250000) 237 220
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t340 : ((59036794871/2500000000000 : ℚ) : ℝ) ≤ stT237 340 := by
  have hc : ((217717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).1
  have hw2 : ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59036794871/2500000000000 : ℚ) : ℝ)
      = ((271163/5000000 : ℚ) : ℝ) * ((217717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c341 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((911369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1060497/10000000) (δ := 11981/1000000000) (ψ := 69893/250000) 237 220
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t341 : ((49350657807/1000000000000 : ℚ) : ℝ) ≤ stT237 341 := by
  have hc : ((911319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49350657807/1000000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((911319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c342 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((481911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16863/250000) (δ := 6011/500000000) (ψ := 69893/250000) 237 220
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t342 : ((65143517967/1250000000000 : ℚ) : ℝ) ≤ stT237 342 := by
  have hc : ((240943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65143517967/1250000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((240943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c343 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((572063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2404443/10000000) (δ := 11981/1000000000) (ψ := 69893/250000) 237 220
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t343 : ((308857847337/10000000000000 : ℚ) : ℝ) ≤ stT237 343 := by
  have hc : ((572013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((308857847337/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((572013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c344 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-80847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4129329/10000000) (δ := 11981/1000000000) (ψ := 69893/250000) 237 220
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t344 : ((-10904187527/2500000000000 : ℚ) : ℝ) ≤ stT237 344 := by
  have hc : ((-80897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).2
  have h0 : (0:ℝ) ≤ ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10904187527/2500000000000 : ℚ) : ℝ)
      = ((134791/2500000 : ℚ) : ℝ) * ((-80897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c345 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-43459/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2924619/5000000) (δ := 11981/1000000000) (ψ := 69893/250000) 237 220
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t345 : ((-93596903127/2500000000000 : ℚ) : ℝ) ≤ stT237 345 := by
  have hc : ((-347697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93596903127/2500000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-347697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c346 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-198657/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756411/1000000) (δ := 6011/500000000) (ψ := 69893/250000) 237 220
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t346 : ((-26701043467/500000000000 : ℚ) : ℝ) ≤ stT237 346 := by
  have hc : ((-198667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26701043467/500000000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-198667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c347 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-842961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3216949/5000000) (δ := 2383/200000000) (ψ := 69893/250000) 237 221
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t347 : ((-452552752119/10000000000000 : ℚ) : ℝ) ≤ stT237 347 := by
  have hc : ((-843011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452552752119/10000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-843011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c348 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-315277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4728861/10000000) (δ := 2403/200000000) (ψ := 69893/250000) 237 221
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t348 : ((-169033245639/10000000000000 : ℚ) : ℝ) ≤ stT237 348 := by
  have hc : ((-315327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169033245639/10000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-315327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c349 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((351641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1514341/5000000) (δ := 2383/200000000) (ψ := 69893/250000) 237 221
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t349 : ((188202091617/10000000000000 : ℚ) : ℝ) ≤ stT237 349 := by
  have hc : ((351591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188202091617/10000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((351591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c350 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((861099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1333421/10000000) (δ := 2383/200000000) (ψ := 69893/250000) 237 221
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t350 : ((230124816789/5000000000000 : ℚ) : ℝ) ≤ stT237 350 := by
  have hc : ((861049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230124816789/5000000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((861049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c351 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((989819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357041/10000000) (δ := 743/62500000) (ψ := 69893/250000) 237 221
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t351 : ((412733673/7812500000 : ℚ) : ℝ) ≤ stT237 351 := by
  have hc : ((989769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).1
  have hw2 : ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((834/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((412733673/7812500000 : ℚ) : ℝ)
      = ((834/15625 : ℚ) : ℝ) * ((989769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c352 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((68437/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 510661/2500000) (δ := 2383/200000000) (ψ := 69893/250000) 237 221
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t352 : ((2279645277/62500000000 : ℚ) : ℝ) ≤ stT237 352 := by
  have hc : ((4277/6250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).1
  have hw2 : ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((533001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2279645277/62500000000 : ℚ) : ℝ)
      = ((533001/10000000 : ℚ) : ℝ) * ((4277/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c353 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((10163/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3723507/10000000) (δ := 2403/200000000) (ψ := 69893/250000) 237 221
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t353 : ((10811779121/2500000000000 : ℚ) : ℝ) ≤ stT237 353 := by
  have hc : ((40627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10811779121/2500000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((40627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c354 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-69447/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5399631/10000000) (δ := 2997/250000000) (ψ := 69893/250000) 237 221
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t354 : ((-29531244087/1000000000000 : ℚ) : ℝ) ≤ stT237 354 := by
  have hc : ((-277813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29531244087/1000000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-277813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c355 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-951349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1414191/2000000) (δ := 2997/250000000) (ψ := 69893/250000) 237 221
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t355 : ((-100990052451/2000000000000 : ℚ) : ℝ) ≤ stT237 355 := by
  have hc : ((-951399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).2
  have h0 : (0:ℝ) ≤ ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100990052451/2000000000000 : ℚ) : ℝ)
      = ((106149/2000000 : ℚ) : ℝ) * ((-951399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c356 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-938177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3485153/5000000) (δ := 2379/200000000) (ψ := 69893/250000) 237 222
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t356 : ((-497259371773/10000000000000 : ℚ) : ℝ) ≤ stT237 356 := by
  have hc : ((-938227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).2
  have h0 : (0:ℝ) ≤ ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-497259371773/10000000000000 : ℚ) : ℝ)
      = ((529999/10000000 : ℚ) : ℝ) * ((-938227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c357 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-131213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -663543/1250000) (δ := 1501/125000000) (ψ := 69893/250000) 237 222
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t357 : ((-138904028907/5000000000000 : ℚ) : ℝ) ≤ stT237 357 := by
  have hc : ((-262451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).2
  have h0 : (0:ℝ) ≤ ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138904028907/5000000000000 : ℚ) : ℝ)
      = ((529257/10000000 : ℚ) : ℝ) * ((-262451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c358 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((110171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3651003/10000000) (δ := 1501/125000000) (ψ := 69893/250000) 237 222
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t358 : ((14550177609/2500000000000 : ℚ) : ℝ) ≤ stT237 358 := by
  have hc : ((110121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).1
  have hw2 : ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((132129/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14550177609/2500000000000 : ℚ) : ℝ)
      = ((132129/2500000 : ℚ) : ℝ) * ((110121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c359 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((697199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1998283/10000000) (δ := 2379/200000000) (ψ := 69893/250000) 237 222
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t359 : ((367940602071/10000000000000 : ℚ) : ℝ) ≤ stT237 359 := by
  have hc : ((697149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).1
  have hw2 : ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((527779/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((367940602071/10000000000000 : ℚ) : ℝ)
      = ((527779/10000000 : ℚ) : ℝ) * ((697149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c360 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((990209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175063/5000000) (δ := 2977/250000000) (ψ := 69893/250000) 237 222
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t360 : ((260929670157/5000000000000 : ℚ) : ℝ) ≤ stT237 360 := by
  have hc : ((990159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).1
  have hw2 : ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260929670157/5000000000000 : ℚ) : ℝ)
      = ((263523/5000000 : ℚ) : ℝ) * ((990159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c361 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((434563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129341/1000000) (δ := 2379/200000000) (ψ := 69893/250000) 237 222
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t361 : ((22870386747/500000000000 : ℚ) : ℝ) ≤ stT237 361 := by
  have hc : ((217269/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).1
  have hw2 : ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((105263/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22870386747/500000000000 : ℚ) : ℝ)
      = ((105263/2000000 : ℚ) : ℝ) * ((217269/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c362 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((387409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2932443/10000000) (δ := 2399/200000000) (ψ := 69893/250000) 237 222
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t362 : ((50897810523/2500000000000 : ℚ) : ℝ) ≤ stT237 362 := by
  have hc : ((387359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50897810523/2500000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((387359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c363 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-253183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4566913/10000000) (δ := 2977/250000000) (ψ := 69893/250000) 237 222
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t363 : ((-2076763833/156250000000 : ℚ) : ℝ) ≤ stT237 363 := by
  have hc : ((-253233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).2
  have h0 : (0:ℝ) ≤ ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2076763833/156250000000 : ℚ) : ℝ)
      = ((8201/156250 : ℚ) : ℝ) * ((-253233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c364 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-98531/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6196881/10000000) (δ := 2399/200000000) (ψ := 69893/250000) 237 222
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t364 : ((-206590439307/5000000000000 : ℚ) : ℝ) ≤ stT237 364 := by
  have hc : ((-394149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).2
  have h0 : (0:ℝ) ≤ ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206590439307/5000000000000 : ℚ) : ℝ)
      = ((524143/10000000 : ℚ) : ℝ) * ((-394149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c365 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-12499/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1955601/2500000) (δ := 1501/125000000) (ψ := 69893/250000) 237 222
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t365 : ((-1635650929/31250000000 : ℚ) : ℝ) ≤ stT237 365 := by
  have hc : ((-99997/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1635650929/31250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-99997/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c366 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-201149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6264479/10000000) (δ := 119/10000000) (ψ := 69893/250000) 237 223
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t366 : ((-210297853007/5000000000000 : ℚ) : ℝ) ≤ stT237 366 := by
  have hc : ((-402323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-210297853007/5000000000000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-402323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c367 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-142181/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4647843/10000000) (δ := 3/250000) (ψ := 69893/250000) 237 223
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t367 : ((-9278870397/625000000000 : ℚ) : ℝ) ≤ stT237 367 := by
  have hc : ((-71103/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9278870397/625000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-71103/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c368 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((349053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3035591/10000000) (δ := 119/10000000) (ψ := 69893/250000) 237 223
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t368 : ((90965188929/5000000000000 : ℚ) : ℝ) ≤ stT237 368 := by
  have hc : ((349003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90965188929/5000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((349003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c369 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((26291/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -356931/2500000) (δ := 3/250000) (ψ := 69893/250000) 237 223
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t369 : ((218971665349/5000000000000 : ℚ) : ℝ) ≤ stT237 369 := by
  have hc : ((420631/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218971665349/5000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((420631/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c370 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((124691/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 87909/5000000) (δ := 3/250000) (ψ := 69893/250000) 237 223
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t370 : ((2074255501/40000000000 : ℚ) : ℝ) ≤ stT237 370 := by
  have hc : ((498739/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2074255501/40000000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((498739/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c371 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((23699/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13867/78125) (δ := 11903/1000000000) (ψ := 69893/250000) 237 223
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t371 : ((98424747333/2500000000000 : ℚ) : ℝ) ≤ stT237 371 := by
  have hc : ((379159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98424747333/2500000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((379159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c372 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((22101/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3369867/10000000) (δ := 3/250000) (ψ := 69893/250000) 237 223
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t372 : ((28640559/2500000000 : ℚ) : ℝ) ≤ stT237 372 := by
  have hc : ((1381/6250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).1
  have hw2 : ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((20739/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28640559/2500000000 : ℚ) : ℝ)
      = ((20739/400000 : ℚ) : ℝ) * ((1381/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c373 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-200863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4960493/10000000) (δ := 11903/1000000000) (ψ := 69893/250000) 237 223
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t373 : ((-13001998691/625000000000 : ℚ) : ℝ) ≤ stT237 373 := by
  have hc : ((-25111/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13001998691/625000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-25111/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c374 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-866387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6546793/10000000) (δ := 119/10000000) (ψ := 69893/250000) 237 223
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t374 : ((-14000755483/312500000000 : ℚ) : ℝ) ≤ stT237 374 := by
  have hc : ((-866437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14000755483/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-866437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c375 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-496979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7579017/10000000) (δ := 1201/100000000) (ψ := 69893/250000) 237 224
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t375 : ((-32081483949/625000000000 : ℚ) : ℝ) ≤ stT237 375 := by
  have hc : ((-124251/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32081483949/625000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-124251/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c376 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-737699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6001131/10000000) (δ := 11993/1000000000) (ψ := 69893/250000) 237 224
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t376 : ((-380465274539/10000000000000 : ℚ) : ℝ) ≤ stT237 376 := by
  have hc : ((-737749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).2
  have h0 : (0:ℝ) ≤ ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-380465274539/10000000000000 : ℚ) : ℝ)
      = ((515711/10000000 : ℚ) : ℝ) * ((-737749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c377 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-3977/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4427451/10000000) (δ := 11993/1000000000) (ψ := 69893/250000) 237 224
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t377 : ((-1024388703/100000000000 : ℚ) : ℝ) ≤ stT237 377 := by
  have hc : ((-1989/10000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).2
  have h0 : (0:ℝ) ≤ ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1024388703/100000000000 : ℚ) : ℝ)
      = ((515027/10000000 : ℚ) : ℝ) * ((-1989/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c378 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((82943/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1428959/5000000) (δ := 1191/100000000) (ψ := 69893/250000) 237 224
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t378 : ((5332011369/250000000000 : ℚ) : ℝ) ≤ stT237 378 := by
  have hc : ((82933/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5332011369/250000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((82933/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c379 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((869311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -646237/5000000) (δ := 11893/1000000000) (ψ := 69893/250000) 237 224
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t379 : ((89301790313/2000000000000 : ℚ) : ℝ) ≤ stT237 379 := by
  have hc : ((869261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89301790313/2000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((869261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c380 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((994227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67191/2500000) (δ := 1201/100000000) (ψ := 69893/250000) 237 224
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t380 : ((510001865053/10000000000000 : ℚ) : ℝ) ≤ stT237 380 := by
  have hc : ((994177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).1
  have hw2 : ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((510001865053/10000000000000 : ℚ) : ℝ)
      = ((512989/10000000 : ℚ) : ℝ) * ((994177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c381 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((744931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1825913/10000000) (δ := 1191/100000000) (ψ := 69893/250000) 237 224
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t381 : ((76322741903/2000000000000 : ℚ) : ℝ) ≤ stT237 381 := by
  have hc : ((744881/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).1
  have hw2 : ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102463/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76322741903/2000000000000 : ℚ) : ℝ)
      = ((102463/2000000 : ℚ) : ℝ) * ((744881/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c382 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((27179/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3379033/10000000) (δ := 11893/1000000000) (ψ := 69893/250000) 237 224
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t382 : ((13902774501/1250000000000 : ℚ) : ℝ) ≤ stT237 382 := by
  have hc : ((108691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).1
  have hw2 : ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13902774501/1250000000000 : ℚ) : ℝ)
      = ((127911/2500000 : ℚ) : ℝ) * ((108691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c383 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-12181/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2464003/5000000) (δ := 1191/100000000) (ψ := 69893/250000) 237 224
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t383 : ((-99600147817/5000000000000 : ℚ) : ℝ) ≤ stT237 383 := by
  have hc : ((-194921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99600147817/5000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-194921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c384 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-851273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6473009/10000000) (δ := 1191/100000000) (ψ := 69893/250000) 237 224
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t384 : ((-434439491453/10000000000000 : ℚ) : ℝ) ≤ stT237 384 := by
  have hc : ((-851323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434439491453/10000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-851323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c385 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-997953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -384699/500000) (δ := 12017/1000000000) (ψ := 69893/250000) 237 225
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t385 : ((-31789389559/625000000000 : ℚ) : ℝ) ≤ stT237 385 := by
  have hc : ((-998003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).2
  have h0 : (0:ℝ) ≤ ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31789389559/625000000000 : ℚ) : ℝ)
      = ((31853/625000 : ℚ) : ℝ) * ((-998003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c386 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-38917/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1231407/2000000) (δ := 12017/1000000000) (ψ := 69893/250000) 237 225
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t386 : ((-39619039093/1000000000000 : ℚ) : ℝ) ≤ stT237 386 := by
  have hc : ((-77839/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).2
  have h0 : (0:ℝ) ≤ ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39619039093/1000000000000 : ℚ) : ℝ)
      = ((508987/10000000 : ℚ) : ℝ) * ((-77839/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c387 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-275229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231203/500000) (δ := 11917/1000000000) (ψ := 69893/250000) 237 225
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t387 : ((-139932298791/10000000000000 : ℚ) : ℝ) ≤ stT237 387 := by
  have hc : ((-275279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139932298791/10000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-275279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c388 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((326689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618999/2000000) (δ := 12017/1000000000) (ψ := 69893/250000) 237 225
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t388 : ((165825801047/10000000000000 : ℚ) : ℝ) ≤ stT237 388 := by
  have hc : ((326639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165825801047/10000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((326639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c389 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((202307/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15699/100000) (δ := 12017/1000000000) (ψ := 69893/250000) 237 225
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t389 : ((10256735739/250000000000 : ℚ) : ℝ) ≤ stT237 389 := by
  have hc : ((404589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10256735739/250000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((404589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c390 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((99981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12179/2500000) (δ := 5943/500000000) (ψ := 69893/250000) 237 225
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t390 : ((6328093393/125000000000 : ℚ) : ℝ) ≤ stT237 390 := by
  have hc : ((12497/12500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6328093393/125000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((12497/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c391 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((208093/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 734279/5000000) (δ := 5943/500000000) (ψ := 69893/250000) 237 225
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t391 : ((210461357081/5000000000000 : ℚ) : ℝ) ≤ stT237 391 := by
  have hc : ((416161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((210461357081/5000000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((416161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c392 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((184533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2981981/10000000) (δ := 11917/1000000000) (ψ := 69893/250000) 237 225
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t392 : ((5824410163/312500000000 : ℚ) : ℝ) ≤ stT237 392 := by
  have hc : ((46127/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5824410163/312500000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((46127/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c393 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-22391/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140361/312500) (δ := 5993/500000000) (ψ := 69893/250000) 237 225
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t393 : ((-1412162983/125000000000 : ℚ) : ℝ) ≤ stT237 393 := by
  have hc : ((-5599/25000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1412162983/125000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-5599/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c394 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-46041/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5997273/10000000) (δ := 12017/1000000000) (ψ := 69893/250000) 237 225
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t394 : ((-185573662929/5000000000000 : ℚ) : ℝ) ≤ stT237 394 := by
  have hc : ((-368353/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185573662929/5000000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-368353/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c395 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-123743/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3749571/5000000) (δ := 12017/1000000000) (ψ := 69893/250000) 237 225
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t395 : ((-49812043107/1000000000000 : ℚ) : ℝ) ≤ stT237 395 := by
  have hc : ((-494997/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49812043107/1000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-494997/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c396 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-22431/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1342137/2000000) (δ := 1503/125000000) (ψ := 69893/250000) 237 226
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t396 : ((-45090527351/1000000000000 : ℚ) : ℝ) ≤ stT237 396 := by
  have hc : ((-89729/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45090527351/1000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-89729/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c397 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-493199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13041/25000) (δ := 1503/125000000) (ψ := 69893/250000) 237 226
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t397 : ((-123777383807/5000000000000 : ℚ) : ℝ) ≤ stT237 397 := by
  have hc : ((-493249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123777383807/5000000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-493249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c398 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((40197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3725789/10000000) (δ := 11879/1000000000) (ψ := 69893/250000) 237 226
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t398 : ((2517046961/625000000000 : ℚ) : ℝ) ≤ stT237 398 := by
  have hc : ((10043/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2517046961/625000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((10043/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c399 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((31253/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2238969/10000000) (δ := 1503/125000000) (ψ := 69893/250000) 237 226
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t399 : ((15644812813/500000000000 : ℚ) : ℝ) ≤ stT237 399 := by
  have hc : ((62501/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15644812813/500000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((62501/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c400 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((477319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -755883/10000000) (δ := 11979/1000000000) (ψ := 69893/250000) 237 226
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t400 : ((238647/5000000 : ℚ) : ℝ) ≤ stT237 400 := by
  have hc : ((238647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((238647/5000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((238647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c401 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((239603/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 723531/10000000) (δ := 1503/125000000) (ψ := 69893/250000) 237 226
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t401 : ((14955718191/312500000000 : ℚ) : ℝ) ≤ stT237 401 := by
  have hc : ((479181/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14955718191/312500000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((479181/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c402 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((318697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2199211/10000000) (δ := 11879/1000000000) (ψ := 69893/250000) 237 226
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t402 : ((4966841709/156250000000 : ℚ) : ℝ) ≤ stT237 402 := by
  have hc : ((19917/31250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4966841709/156250000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((19917/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c403 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((102107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3671277/10000000) (δ := 11979/1000000000) (ψ := 69893/250000) 237 226
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t403 : ((10167632739/2000000000000 : ℚ) : ℝ) ≤ stT237 403 := by
  have hc : ((102057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).1
  have hw2 : ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((99627/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10167632739/2000000000000 : ℚ) : ℝ)
      = ((99627/2000000 : ℚ) : ℝ) * ((102057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c404 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-14571/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 513967/1000000) (δ := 11879/1000000000) (ψ := 69893/250000) 237 226
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t404 : ((-116002027559/5000000000000 : ℚ) : ℝ) ≤ stT237 404 := by
  have hc : ((-233161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116002027559/5000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-233161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c405 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-109709/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6604449/10000000) (δ := 1503/125000000) (ψ := 69893/250000) 237 226
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t405 : ((-27258973293/625000000000 : ℚ) : ℝ) ≤ stT237 405 := by
  have hc : ((-438861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27258973293/625000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-438861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c406 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-996419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -152847/200000) (δ := 12031/1000000000) (ψ := 69893/250000) 237 227
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t406 : ((-123634898237/2500000000000 : ℚ) : ℝ) ≤ stT237 406 := by
  have hc : ((-996469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123634898237/2500000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-996469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c407 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-157053/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7731/12500) (δ := 12031/1000000000) (ψ := 69893/250000) 237 227
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t407 : ((-38926650983/1000000000000 : ℚ) : ℝ) ≤ stT237 407 := by
  have hc : ((-157063/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38926650983/1000000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-157063/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c408 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-158007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -946161/2000000) (δ := 12031/1000000000) (ψ := 69893/250000) 237 227
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t408 : ((-2444922949/156250000000 : ℚ) : ℝ) ≤ stT237 408 := by
  have hc : ((-9877/31250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2444922949/156250000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-9877/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c409 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((7993/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656073/2000000) (δ := 12031/1000000000) (ψ := 69893/250000) 237 227
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t409 : ((15806040471/1250000000000 : ℚ) : ℝ) ≤ stT237 409 := by
  have hc : ((127863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15806040471/1250000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((127863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c410 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((185727/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -45837/250000) (δ := 12031/1000000000) (ψ := 69893/250000) 237 227
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t410 : ((22929426457/625000000000 : ℚ) : ℝ) ≤ stT237 410 := by
  have hc : ((371429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22929426457/625000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((371429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c411 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((987851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -390091/10000000) (δ := 11931/1000000000) (ψ := 69893/250000) 237 227
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t411 : ((487245684663/10000000000000 : ℚ) : ℝ) ≤ stT237 411 := by
  have hc : ((987801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((487245684663/10000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((987801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c412 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((913131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1049743/10000000) (δ := 371/31250000) (ψ := 69893/250000) 237 227
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t412 : ((56230267223/1250000000000 : ℚ) : ℝ) ≤ stT237 412 := by
  have hc : ((913081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56230267223/1250000000000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((913081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c413 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((544979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1243041/5000000) (δ := 12031/1000000000) (ψ := 69893/250000) 237 227
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t413 : ((268141578243/10000000000000 : ℚ) : ℝ) ≤ stT237 413 := by
  have hc : ((544929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268141578243/10000000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((544929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c414 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((3203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 489873/1250000) (δ := 12031/1000000000) (ψ := 69893/250000) 237 227
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t414 : ((1549614369/10000000000000 : ℚ) : ℝ) ≤ stT237 414 := by
  have hc : ((3153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1549614369/10000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((3153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c415 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-538439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5348449/10000000) (δ := 371/31250000) (ψ := 69893/250000) 237 227
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t415 : ((-264334018809/10000000000000 : ℚ) : ℝ) ≤ stT237 415 := by
  have hc : ((-538489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264334018809/10000000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-538489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c416 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-908203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6774419/10000000) (δ := 11931/1000000000) (ψ := 69893/250000) 237 227
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t416 : ((-445308271623/10000000000000 : ℚ) : ℝ) ≤ stT237 416 := by
  have hc : ((-908253/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-445308271623/10000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-908253/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c417 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-990601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -938869/1250000) (δ := 2373/200000000) (ψ := 69893/250000) 237 228
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t417 : ((-485124766653/10000000000000 : ℚ) : ℝ) ≤ stT237 417 := by
  have hc : ((-990651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485124766653/10000000000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-990651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c418 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-761693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1522949/2500000) (δ := 2373/200000000) (ψ := 69893/250000) 237 228
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t418 : ((-93145172297/2500000000000 : ℚ) : ℝ) ≤ stT237 418 := by
  have hc : ((-761743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93145172297/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-761743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c419 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-73787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4676017/10000000) (δ := 5969/500000000) (ψ := 69893/250000) 237 228
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t419 : ((-18026708667/1250000000000 : ℚ) : ℝ) ≤ stT237 419 := by
  have hc : ((-147599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18026708667/1250000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-147599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c420 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((262247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25497/78125) (δ := 2393/200000000) (ψ := 69893/250000) 237 228
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t420 : ((2558780523/200000000000 : ℚ) : ℝ) ≤ stT237 420 := by
  have hc : ((262197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).1
  have hw2 : ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2558780523/200000000000 : ℚ) : ℝ)
      = ((9759/200000 : ℚ) : ℝ) * ((262197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c421 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((737229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1854591/10000000) (δ := 6019/500000000) (ψ := 69893/250000) 237 228
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t421 : ((35927892923/1000000000000 : ℚ) : ℝ) ≤ stT237 421 := by
  have hc : ((737179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35927892923/1000000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((737179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c422 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((983923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -89777/2000000) (δ := 5969/500000000) (ψ := 69893/250000) 237 228
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t422 : ((59867688177/1250000000000 : ℚ) : ℝ) ≤ stT237 422 := by
  have hc : ((983873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59867688177/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((983873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c423 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((928153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 238361/2500000) (δ := 5969/500000000) (ψ := 69893/250000) 237 228
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t423 : ((56407316031/1250000000000 : ℚ) : ℝ) ≤ stT237 423 := by
  have hc : ((928103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56407316031/1250000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((928103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c424 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((36811/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1176257/5000000) (δ := 2373/200000000) (ψ := 69893/250000) 237 228
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t424 : ((71501800123/2500000000000 : ℚ) : ℝ) ≤ stT237 424 := by
  have hc : ((294463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((71501800123/2500000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((294463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c425 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((71429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1874133/5000000) (δ := 2393/200000000) (ψ := 69893/250000) 237 228
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t425 : ((34623882909/10000000000000 : ℚ) : ℝ) ≤ stT237 425 := by
  have hc : ((71379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34623882909/10000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((71379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c426 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-466657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128519/250000) (δ := 5969/500000000) (ψ := 69893/250000) 237 228
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t426 : ((-113060237457/5000000000000 : ℚ) : ℝ) ≤ stT237 426 := by
  have hc : ((-466707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).2
  have h0 : (0:ℝ) ≤ ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113060237457/5000000000000 : ℚ) : ℝ)
      = ((242251/5000000 : ℚ) : ℝ) * ((-466707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c427 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-215753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1305999/2000000) (δ := 6019/500000000) (ψ := 69893/250000) 237 228
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t427 : ((-104416261477/2500000000000 : ℚ) : ℝ) ≤ stT237 427 := by
  have hc : ((-431531/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104416261477/2500000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-431531/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c428 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-999693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1948013/2500000) (δ := 11857/1000000000) (ψ := 69893/250000) 237 229
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t428 : ((-483244774167/10000000000000 : ℚ) : ℝ) ≤ stT237 428 := by
  have hc : ((-999743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-483244774167/10000000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-999743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c429 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-837621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -256371/400000) (δ := 6023/500000000) (ψ := 69893/250000) 237 229
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t429 : ((-80886349431/2000000000000 : ℚ) : ℝ) ≤ stT237 429 := by
  have hc : ((-837671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80886349431/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-837671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c430 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-426941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2514879/5000000) (δ := 11957/1000000000) (ψ := 69893/250000) 237 229
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t430 : ((-205913420813/10000000000000 : ℚ) : ℝ) ≤ stT237 430 := by
  have hc : ((-426991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205913420813/10000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-426991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c431 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((109179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3653499/10000000) (δ := 11957/1000000000) (ψ := 69893/250000) 237 229
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t431 : ((52565584107/10000000000000 : ℚ) : ℝ) ≤ stT237 431 := by
  have hc : ((109129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52565584107/10000000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((109129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c432 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((122409/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -114019/500000) (δ := 11857/1000000000) (ψ := 69893/250000) 237 229
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t432 : ((471113751/16000000000 : ℚ) : ℝ) ≤ stT237 432 := by
  have hc : ((122399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471113751/16000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((122399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c433 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((934423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -910401/10000000) (δ := 6023/500000000) (ψ := 69893/250000) 237 229
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t433 : ((449030698237/10000000000000 : ℚ) : ℝ) ≤ stT237 433 := by
  have hc : ((934373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449030698237/10000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((934373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c434 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((122923/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228189/5000000) (δ := 6023/500000000) (ψ := 69893/250000) 237 229
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t434 : ((47201507001/1000000000000 : ℚ) : ℝ) ≤ stT237 434 := by
  have hc : ((491667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47201507001/1000000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((491667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c435 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((373251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 113751/625000) (δ := 11957/1000000000) (ψ := 69893/250000) 237 229
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t435 : ((89474028819/2500000000000 : ℚ) : ℝ) ≤ stT237 435 := by
  have hc : ((186613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89474028819/2500000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((186613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c436 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((294173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 636103/2000000) (δ := 5973/500000000) (ψ := 69893/250000) 237 229
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t436 : ((140859328299/10000000000000 : ℚ) : ℝ) ≤ stT237 436 := by
  have hc : ((294123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((140859328299/10000000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((294123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c437 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-30241/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4537873/10000000) (δ := 11857/1000000000) (ψ := 69893/250000) 237 229
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t437 : ((-11575380597/1000000000000 : ℚ) : ℝ) ≤ stT237 437 := by
  have hc : ((-120989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11575380597/1000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-120989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c438 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-353797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 589221/1000000) (δ := 6023/500000000) (ψ := 69893/250000) 237 229
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t438 : ((-84531437109/2500000000000 : ℚ) : ℝ) ≤ stT237 438 := by
  have hc : ((-176911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84531437109/2500000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-176911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c439 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-242581/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3621703/5000000) (δ := 5973/500000000) (ψ := 69893/250000) 237 229
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t439 : ((-115783570119/2500000000000 : ℚ) : ℝ) ≤ stT237 439 := by
  have hc : ((-485187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).2
  have h0 : (0:ℝ) ≤ ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115783570119/2500000000000 : ℚ) : ℝ)
      = ((238637/5000000 : ℚ) : ℝ) * ((-485187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c440 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-478399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3558221/5000000) (δ := 11953/1000000000) (ψ := 69893/250000) 237 230
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t440 : ((-7127500949/156250000000 : ℚ) : ℝ) ≤ stT237 440 := by
  have hc : ((-59803/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7127500949/156250000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-59803/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c441 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-672637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -360713/625000) (δ := 11853/1000000000) (ψ := 69893/250000) 237 230
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t441 : ((-320327495217/10000000000000 : ℚ) : ℝ) ≤ stT237 441 := by
  have hc : ((-672687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320327495217/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-672687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c442 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-49903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1107349/2500000) (δ := 241/20000000) (ψ := 69893/250000) 237 230
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t442 : ((-11871203703/1250000000000 : ℚ) : ℝ) ≤ stT237 442 := by
  have hc : ((-99831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11871203703/1250000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-99831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c443 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((41053/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -618081/2000000) (δ := 239/20000000) (ψ := 69893/250000) 237 230
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t443 : ((39003771159/2500000000000 : ℚ) : ℝ) ≤ stT237 443 := by
  have hc : ((164187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).1
  have hw2 : ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237557/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39003771159/2500000000000 : ℚ) : ℝ)
      = ((237557/5000000 : ℚ) : ℝ) * ((164187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c444 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((381849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -438609/2500000) (δ := 239/20000000) (ψ := 69893/250000) 237 230
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t444 : ((707833087/19531250000 : ℚ) : ℝ) ≤ stT237 444 := by
  have hc : ((11932/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).1
  have hw2 : ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((237289/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((707833087/19531250000 : ℚ) : ℝ)
      = ((237289/5000000 : ℚ) : ℝ) * ((11932/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c445 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((985821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421489/10000000) (δ := 241/20000000) (ψ := 69893/250000) 237 230
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t445 : ((93459962739/2000000000000 : ℚ) : ℝ) ≤ stT237 445 := by
  have hc : ((985771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).1
  have hw2 : ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94809/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93459962739/2000000000000 : ℚ) : ℝ)
      = ((94809/2000000 : ℚ) : ℝ) * ((985771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c446 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((467347/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56781/625000) (δ := 239/20000000) (ψ := 69893/250000) 237 230
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t446 : ((110641521093/2500000000000 : ℚ) : ℝ) ≤ stT237 446 := by
  have hc : ((233661/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110641521093/2500000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((233661/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c447 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((156539/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2235459/10000000) (δ := 239/20000000) (ψ := 69893/250000) 237 230
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t447 : ((148068747099/5000000000000 : ℚ) : ℝ) ≤ stT237 447 := by
  have hc : ((313053/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148068747099/5000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((313053/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c448 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((7323/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3559519/10000000) (δ := 11853/1000000000) (ψ := 69893/250000) 237 230
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t448 : ((1383442731/200000000000 : ℚ) : ℝ) ≤ stT237 448 := by
  have hc : ((14641/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1383442731/200000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((14641/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c449 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-74449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4880557/10000000) (δ := 11853/1000000000) (ψ := 69893/250000) 237 230
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t449 : ((-3513943587/200000000000 : ℚ) : ℝ) ≤ stT237 449 := by
  have hc : ((-74459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).2
  have h0 : (0:ℝ) ≤ ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3513943587/200000000000 : ℚ) : ℝ)
      = ((47193/1000000 : ℚ) : ℝ) * ((-74459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c450 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-788693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1549673/2500000) (δ := 11953/1000000000) (ψ := 69893/250000) 237 230
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t450 : ((-74363478783/2000000000000 : ℚ) : ℝ) ≤ stT237 450 := by
  have hc : ((-788743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).2
  have h0 : (0:ℝ) ≤ ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74363478783/2000000000000 : ℚ) : ℝ)
      = ((94281/2000000 : ℚ) : ℝ) * ((-788743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c451 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-990763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7513923/10000000) (δ := 239/20000000) (ψ := 69893/250000) 237 230
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t451 : ((-233278003533/5000000000000 : ℚ) : ℝ) ≤ stT237 451 := by
  have hc : ((-990813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).2
  have h0 : (0:ℝ) ≤ ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233278003533/5000000000000 : ℚ) : ℝ)
      = ((235441/5000000 : ℚ) : ℝ) * ((-990813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c452 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-925333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6881771/10000000) (δ := 593/50000000) (ψ := 69893/250000) 237 231
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t452 : ((-435264073263/10000000000000 : ℚ) : ℝ) ≤ stT237 452 := by
  have hc : ((-925383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-435264073263/10000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-925383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c453 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-9557/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2786173/5000000) (δ := 593/50000000) (ψ := 69893/250000) 237 231
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t453 : ((-143700400009/5000000000000 : ℚ) : ℝ) ≤ stT237 453 := by
  have hc : ((-305849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143700400009/5000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-305849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c454 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-67571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1066471/2500000) (δ := 12043/1000000000) (ψ := 69893/250000) 237 231
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t454 : ((-1982776569/312500000000 : ℚ) : ℝ) ≤ stT237 454 := by
  have hc : ((-16899/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1982776569/312500000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-16899/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c455 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((188203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1481103/5000000) (δ := 11943/1000000000) (ψ := 69893/250000) 237 231
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t455 : ((44109581823/2500000000000 : ℚ) : ℝ) ≤ stT237 455 := by
  have hc : ((94089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).1
  have hw2 : ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((468807/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44109581823/2500000000000 : ℚ) : ℝ)
      = ((468807/10000000 : ℚ) : ℝ) * ((94089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c456 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((787181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1661431/10000000) (δ := 299/25000000) (ψ := 69893/250000) 237 231
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t456 : ((92151787563/2500000000000 : ℚ) : ℝ) ≤ stT237 456 := by
  have hc : ((787131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).1
  have hw2 : ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117073/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92151787563/2500000000000 : ℚ) : ℝ)
      = ((117073/2500000 : ℚ) : ℝ) * ((787131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c457 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((197889/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9089/250000) (δ := 593/50000000) (ψ := 69893/250000) 237 231
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t457 : ((4628191931/100000000000 : ℚ) : ℝ) ≤ stT237 457 := by
  have hc : ((197879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4628191931/100000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((197879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c458 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((46569/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 465763/5000000) (δ := 12043/1000000000) (ψ := 69893/250000) 237 231
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t458 : ((43518163777/1000000000000 : ℚ) : ℝ) ≤ stT237 458 := by
  have hc : ((93133/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43518163777/1000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((93133/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c459 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((39361/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 555957/2500000) (δ := 11943/1000000000) (ψ := 69893/250000) 237 231
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t459 : ((3674136347/125000000000 : ℚ) : ℝ) ≤ stT237 459 := by
  have hc : ((314863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3674136347/125000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((314863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c460 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((164751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3513227/10000000) (δ := 299/25000000) (ψ := 69893/250000) 237 231
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t460 : ((19198042663/2500000000000 : ℚ) : ℝ) ≤ stT237 460 := by
  have hc : ((164701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19198042663/2500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((164701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c461 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-10691/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47999/100000) (δ := 299/25000000) (ψ := 69893/250000) 237 231
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t461 : ((-79680462507/5000000000000 : ℚ) : ℝ) ≤ stT237 461 := by
  have hc : ((-171081/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79680462507/5000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-171081/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c462 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-379799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6083729/10000000) (δ := 299/25000000) (ψ := 69893/250000) 237 231
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t462 : ((-11044403577/312500000000 : ℚ) : ℝ) ≤ stT237 462 := by
  have hc : ((-23739/31250 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11044403577/312500000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-23739/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c463 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-24523/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 230151/312500) (δ := 11943/1000000000) (ψ := 69893/250000) 237 231
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t463 : ((-2279479989/50000000000 : ℚ) : ℝ) ≤ stT237 463 := by
  have hc : ((-98097/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2279479989/50000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-98097/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c464 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-950589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1766203/2500000) (δ := 11967/1000000000) (ψ := 69893/250000) 237 232
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t464 : ((-441323698721/10000000000000 : ℚ) : ℝ) ≤ stT237 464 := by
  have hc : ((-950639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441323698721/10000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-950639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c465 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-169473/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5789219/10000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 232
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t465 : ((-157194072569/5000000000000 : ℚ) : ℝ) ≤ stT237 465 := by
  have hc : ((-338971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-157194072569/5000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-338971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c466 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-23359/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4516411/10000000) (δ := 3009/250000000) (ψ := 69893/250000) 237 232
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t466 : ((-1352898261/125000000000 : ℚ) : ℝ) ≤ stT237 466 := by
  have hc : ((-5841/25000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1352898261/125000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-5841/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c467 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((134457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405791/1250000) (δ := 3009/250000000) (ψ := 69893/250000) 237 232
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t467 : ((242998443/19531250000 : ℚ) : ℝ) ≤ stT237 467 := by
  have hc : ((4201/15625 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242998443/19531250000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((4201/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c468 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((175679/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -197897/1000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 232
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t468 : ((649614717/20000000000 : ℚ) : ℝ) ≤ stT237 468 := by
  have hc : ((351333/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((649614717/20000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((351333/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c469 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((959461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -714279/10000000) (δ := 373/31250000) (ψ := 69893/250000) 237 232
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t469 : ((443014745127/10000000000000 : ℚ) : ℝ) ≤ stT237 469 := by
  have hc : ((959411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((443014745127/10000000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((959411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c470 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((976099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 547687/10000000) (δ := 11867/1000000000) (ψ := 69893/250000) 237 232
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t470 : ((90043448397/2000000000000 : ℚ) : ℝ) ≤ stT237 470 := by
  have hc : ((976049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).1
  have hw2 : ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((92253/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90043448397/2000000000000 : ℚ) : ℝ)
      = ((92253/2000000 : ℚ) : ℝ) * ((976049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c471 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((18749/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 903493/5000000) (δ := 3009/250000000) (ψ := 69893/250000) 237 232
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t471 : ((1382159121/40000000000 : ℚ) : ℝ) ≤ stT237 471 := by
  have hc : ((74991/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).1
  have hw2 : ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18431/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1382159121/40000000000 : ℚ) : ℝ)
      = ((18431/400000 : ℚ) : ℝ) * ((74991/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c472 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((84631/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 153181/500000) (δ := 11967/1000000000) (ψ := 69893/250000) 237 232
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t472 : ((77897591019/5000000000000 : ℚ) : ℝ) ≤ stT237 472 := by
  have hc : ((169237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).1
  have hw2 : ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77897591019/5000000000000 : ℚ) : ℝ)
      = ((460287/10000000 : ℚ) : ℝ) * ((169237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c473 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-38901/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4317587/10000000) (δ := 11967/1000000000) (ψ := 69893/250000) 237 232
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t473 : ((-35784932427/5000000000000 : ℚ) : ℝ) ≤ stT237 473 := by
  have hc : ((-77827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35784932427/5000000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-77827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c474 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-152643/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5568947/10000000) (δ := 11967/1000000000) (ψ := 69893/250000) 237 232
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t474 : ((-35058556819/1250000000000 : ℚ) : ℝ) ≤ stT237 474 := by
  have hc : ((-305311/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35058556819/1250000000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-305311/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c475 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-915303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170441/250000) (δ := 3009/250000000) (ψ := 69893/250000) 237 232
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t475 : ((-26249577981/625000000000 : ℚ) : ℝ) ≤ stT237 475 := by
  have hc : ((-915353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).2
  have h0 : (0:ℝ) ≤ ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26249577981/625000000000 : ℚ) : ℝ)
      = ((28677/625000 : ℚ) : ℝ) * ((-915353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c476 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-199297/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1528859/2000000) (δ := 5987/500000000) (ψ := 69893/250000) 237 233
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t476 : ((-1827047269/40000000000 : ℚ) : ℝ) ≤ stT237 476 := by
  have hc : ((-199307/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).2
  have h0 : (0:ℝ) ≤ ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1827047269/40000000000 : ℚ) : ℝ)
      = ((9167/200000 : ℚ) : ℝ) * ((-199307/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c477 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-835781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51207/80000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 233
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t477 : ((-382701104139/10000000000000 : ℚ) : ℝ) ≤ stT237 477 := by
  have hc : ((-835831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).2
  have h0 : (0:ℝ) ≤ ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-382701104139/10000000000000 : ℚ) : ℝ)
      = ((457869/10000000 : ℚ) : ℝ) * ((-835831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c478 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-473451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2580001/5000000) (δ := 5937/500000000) (ψ := 69893/250000) 237 233
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t478 : ((-21657462239/1000000000000 : ℚ) : ℝ) ≤ stT237 478 := by
  have hc : ((-473501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).2
  have h0 : (0:ℝ) ≤ ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21657462239/1000000000000 : ℚ) : ℝ)
      = ((45739/1000000 : ℚ) : ℝ) * ((-473501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c479 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((1039/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -980449/2500000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 233
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t479 : ((231653877/2500000000000 : ℚ) : ℝ) ≤ stT237 479 := by
  have hc : ((507/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((231653877/2500000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((507/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c480 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((59529/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1343039/5000000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 233
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t480 : ((21734613117/1000000000000 : ℚ) : ℝ) ≤ stT237 480 := by
  have hc : ((238091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).1
  have hw2 : ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21734613117/1000000000000 : ℚ) : ℝ)
      = ((91287/2000000 : ℚ) : ℝ) * ((238091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c481 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((835799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -726513/5000000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 233
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t481 : ((9526702851/250000000000 : ℚ) : ℝ) ≤ stT237 481 := by
  have hc : ((835749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).1
  have hw2 : ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11399/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9526702851/250000000000 : ℚ) : ℝ)
      = ((11399/250000 : ℚ) : ℝ) * ((835749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c482 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((996043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222463/10000000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 233
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t482 : ((453661863591/10000000000000 : ℚ) : ℝ) ≤ stT237 482 := by
  have hc : ((995993/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).1
  have hw2 : ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((455487/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453661863591/10000000000000 : ℚ) : ℝ)
      = ((455487/10000000 : ℚ) : ℝ) * ((995993/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c483 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((920203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 502747/5000000) (δ := 5987/500000000) (ψ := 69893/250000) 237 233
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t483 : ((83736683459/2000000000000 : ℚ) : ℝ) ≤ stT237 483 := by
  have hc : ((920153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).1
  have hw2 : ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83736683459/2000000000000 : ℚ) : ℝ)
      = ((91003/2000000 : ℚ) : ℝ) * ((920153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c484 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((627557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2230961/10000000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 233
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t484 : ((57046033863/2000000000000 : ℚ) : ℝ) ≤ stT237 484 := by
  have hc : ((627507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57046033863/2000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((627507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c485 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((9407/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1726911/5000000) (δ := 11929/1000000000) (ψ := 69893/250000) 237 233
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t485 : ((2135178871/250000000000 : ℚ) : ℝ) ≤ stT237 485 := by
  have hc : ((18809/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2135178871/250000000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((18809/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c486 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-147237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2337127/5000000) (δ := 5987/500000000) (ψ := 69893/250000) 237 233
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t486 : ((-3339975791/250000000000 : ℚ) : ℝ) ≤ stT237 486 := by
  have hc : ((-73631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3339975791/250000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-73631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c487 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-353787/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5892137/10000000) (δ := 12029/1000000000) (ψ := 69893/250000) 237 233
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t487 : ((-5010243279/156250000000 : ℚ) : ℝ) ≤ stT237 487 := by
  have hc : ((-88453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).2
  have h0 : (0:ℝ) ≤ ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5010243279/156250000000 : ℚ) : ℝ)
      = ((56643/1250000 : ℚ) : ℝ) * ((-88453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c488 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-191151/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7107533/10000000) (δ := 5987/500000000) (ψ := 69893/250000) 237 233
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t488 : ((-86534570319/2000000000000 : ℚ) : ℝ) ≤ stT237 488 := by
  have hc : ((-191161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).2
  have h0 : (0:ℝ) ≤ ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86534570319/2000000000000 : ℚ) : ℝ)
      = ((452679/10000000 : ℚ) : ℝ) * ((-191161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c489 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-122831/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7387583/10000000) (δ := 5941/500000000) (ψ := 69893/250000) 237 234
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t489 : ((-27774484923/625000000000 : ℚ) : ℝ) ≤ stT237 489 := by
  have hc : ((-491349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27774484923/625000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-491349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c490 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-78337/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1235433/2000000) (δ := 11921/1000000000) (ψ := 69893/250000) 237 234
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t490 : ((-8847827967/250000000000 : ℚ) : ℝ) ≤ stT237 490 := by
  have hc : ((-39171/50000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8847827967/250000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-39171/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c491 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-50613/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -621147/1250000) (δ := 11921/1000000000) (ψ := 69893/250000) 237 234
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t491 : ((-45688327619/2500000000000 : ℚ) : ℝ) ≤ stT237 491 := by
  have hc : ((-202477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45688327619/2500000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-202477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c492 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((204/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150547/400000) (δ := 5991/500000000) (ψ := 69893/250000) 237 234
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t492 : ((1470395091/500000000000 : ℚ) : ℝ) ≤ stT237 492 := by
  have hc : ((6523/100000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1470395091/500000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((6523/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c493 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((519727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2560663/10000000) (δ := 5991/500000000) (ψ := 69893/250000) 237 234
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t493 : ((234050568229/10000000000000 : ℚ) : ℝ) ≤ stT237 493 := by
  have hc : ((519677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234050568229/10000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((519677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c494 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((855641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1360021/10000000) (δ := 5991/500000000) (ψ := 69893/250000) 237 234
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t494 : ((384948358311/10000000000000 : ℚ) : ℝ) ≤ stT237 494 := by
  have hc : ((855591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384948358311/10000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((855591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c495 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((199581/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40467/2500000) (δ := 11921/1000000000) (ψ := 69893/250000) 237 234
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t495 : ((44850189543/1000000000000 : ℚ) : ℝ) ≤ stT237 495 := by
  have hc : ((199571/200000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44850189543/1000000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((199571/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c496 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((915693/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 258479/2500000) (δ := 5991/500000000) (ψ := 69893/250000) 237 234
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t496 : ((411135610359/10000000000000 : ℚ) : ℝ) ≤ stT237 496 := by
  have hc : ((915643/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((411135610359/10000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((915643/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c497 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((314353/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 222727/1000000) (δ := 5941/500000000) (ψ := 69893/250000) 237 234
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t497 : ((17624410251/625000000000 : ℚ) : ℝ) ≤ stT237 497 := by
  have hc : ((39291/62500 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17624410251/625000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((39291/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c498 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((50529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 683639/2000000) (δ := 5941/500000000) (ψ := 69893/250000) 237 234
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t498 : ((4527389763/500000000000 : ℚ) : ℝ) ≤ stT237 498 := by
  have hc : ((101033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).1
  have hw2 : ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((44811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4527389763/500000000000 : ℚ) : ℝ)
      = ((44811/1000000 : ℚ) : ℝ) * ((101033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c499 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-134283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18427/40000) (δ := 5941/500000000) (ψ := 69893/250000) 237 234
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t499 : ((-7515573487/625000000000 : ℚ) : ℝ) ≤ stT237 499 := by
  have hc : ((-33577/125000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7515573487/625000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-33577/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_c500 :
    |Real.cos (((237 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((-84873/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1158587/2000000) (δ := 5941/500000000) (ψ := 69893/250000) 237 234
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st237_t500 : ((-75918377819/2500000000000 : ℚ) : ℝ) ≤ stT237 500 := by
  have hc : ((-339517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((237 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((69893/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st237_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75918377819/2500000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-339517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st237_p1 : ((240281/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT237 (i+1) := by
  rw [Finset.sum_range_one]
  exact st237_t1

theorem st237_p2 : ((95687214479/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT237 (i+1))
      = (∑ i ∈ Finset.range 1, stT237 (i+1)) + stT237 2 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 1
    simpa using h
  have hprev := st237_p1
  have hstep := st237_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p3 : ((5375488477363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT237 (i+1))
      = (∑ i ∈ Finset.range 2, stT237 (i+1)) + stT237 3 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 2
    simpa using h
  have hprev := st237_p2
  have hstep := st237_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p4 : ((5435965977363/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT237 (i+1))
      = (∑ i ∈ Finset.range 3, stT237 (i+1)) + stT237 4 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 3
    simpa using h
  have hprev := st237_p3
  have hstep := st237_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p5 : ((4274178834807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT237 (i+1))
      = (∑ i ∈ Finset.range 4, stT237 (i+1)) + stT237 5 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 4
    simpa using h
  have hprev := st237_p4
  have hstep := st237_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p6 : ((2297514050901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT237 (i+1))
      = (∑ i ∈ Finset.range 5, stT237 (i+1)) + stT237 6 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 5
    simpa using h
  have hprev := st237_p5
  have hstep := st237_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p7 : ((2284020861227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT237 (i+1))
      = (∑ i ∈ Finset.range 6, stT237 (i+1)) + stT237 7 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 6
    simpa using h
  have hprev := st237_p6
  have hstep := st237_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p8 : ((-460904096761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT237 (i+1))
      = (∑ i ∈ Finset.range 7, stT237 (i+1)) + stT237 8 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 7
    simpa using h
  have hprev := st237_p7
  have hstep := st237_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p9 : ((1221342401681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT237 (i+1))
      = (∑ i ∈ Finset.range 8, stT237 (i+1)) + stT237 9 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 8
    simpa using h
  have hprev := st237_p8
  have hstep := st237_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p10 : ((471030304363/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT237 (i+1))
      = (∑ i ∈ Finset.range 9, stT237 (i+1)) + stT237 10 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 9
    simpa using h
  have hprev := st237_p9
  have hstep := st237_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p11 : ((-122072170813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT237 (i+1))
      = (∑ i ∈ Finset.range 10, stT237 (i+1)) + stT237 11 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 10
    simpa using h
  have hprev := st237_p10
  have hstep := st237_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p12 : ((-252098915257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT237 (i+1))
      = (∑ i ∈ Finset.range 11, stT237 (i+1)) + stT237 12 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 11
    simpa using h
  have hprev := st237_p11
  have hstep := st237_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p13 : ((-2039770699257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT237 (i+1))
      = (∑ i ∈ Finset.range 12, stT237 (i+1)) + stT237 13 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 12
    simpa using h
  have hprev := st237_p12
  have hstep := st237_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p14 : ((-4712517329907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT237 (i+1))
      = (∑ i ∈ Finset.range 13, stT237 (i+1)) + stT237 14 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 13
    simpa using h
  have hprev := st237_p13
  have hstep := st237_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p15 : ((-105878213271/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT237 (i+1))
      = (∑ i ∈ Finset.range 14, stT237 (i+1)) + stT237 15 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 14
    simpa using h
  have hprev := st237_p14
  have hstep := st237_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p16 : ((-5080621305241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT237 (i+1))
      = (∑ i ∈ Finset.range 15, stT237 (i+1)) + stT237 16 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 15
    simpa using h
  have hprev := st237_p15
  have hstep := st237_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p17 : ((-3999751702417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT237 (i+1))
      = (∑ i ∈ Finset.range 16, stT237 (i+1)) + stT237 17 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 16
    simpa using h
  have hprev := st237_p16
  have hstep := st237_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p18 : ((-1662330697369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT237 (i+1))
      = (∑ i ∈ Finset.range 17, stT237 (i+1)) + stT237 18 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 17
    simpa using h
  have hprev := st237_p17
  have hstep := st237_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p19 : ((307758570259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT237 (i+1))
      = (∑ i ∈ Finset.range 18, stT237 (i+1)) + stT237 19 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 18
    simpa using h
  have hprev := st237_p18
  have hstep := st237_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p20 : ((2757483732957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT237 (i+1))
      = (∑ i ∈ Finset.range 19, stT237 (i+1)) + stT237 20 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 19
    simpa using h
  have hprev := st237_p19
  have hstep := st237_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p21 : ((670716113701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT237 (i+1))
      = (∑ i ∈ Finset.range 20, stT237 (i+1)) + stT237 21 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 20
    simpa using h
  have hprev := st237_p20
  have hstep := st237_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p22 : ((1320762108697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT237 (i+1))
      = (∑ i ∈ Finset.range 21, stT237 (i+1)) + stT237 22 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 21
    simpa using h
  have hprev := st237_p21
  have hstep := st237_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p23 : ((1640702433769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT237 (i+1))
      = (∑ i ∈ Finset.range 22, stT237 (i+1)) + stT237 23 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 22
    simpa using h
  have hprev := st237_p22
  have hstep := st237_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p24 : ((2633076240811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT237 (i+1))
      = (∑ i ∈ Finset.range 23, stT237 (i+1)) + stT237 24 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 23
    simpa using h
  have hprev := st237_p23
  have hstep := st237_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p25 : ((629172776723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT237 (i+1))
      = (∑ i ∈ Finset.range 24, stT237 (i+1)) + stT237 25 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 24
    simpa using h
  have hprev := st237_p24
  have hstep := st237_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p26 : ((1205491315149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT237 (i+1))
      = (∑ i ∈ Finset.range 25, stT237 (i+1)) + stT237 26 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 25
    simpa using h
  have hprev := st237_p25
  have hstep := st237_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p27 : ((2127124506301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT237 (i+1))
      = (∑ i ∈ Finset.range 26, stT237 (i+1)) + stT237 27 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 26
    simpa using h
  have hprev := st237_p26
  have hstep := st237_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p28 : ((971864367463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT237 (i+1))
      = (∑ i ∈ Finset.range 27, stT237 (i+1)) + stT237 28 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 27
    simpa using h
  have hprev := st237_p27
  have hstep := st237_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p29 : ((2793535260463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT237 (i+1))
      = (∑ i ∈ Finset.range 28, stT237 (i+1)) + stT237 29 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 28
    simpa using h
  have hprev := st237_p28
  have hstep := st237_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p30 : ((704894863957/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT237 (i+1))
      = (∑ i ∈ Finset.range 29, stT237 (i+1)) + stT237 30 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 29
    simpa using h
  have hprev := st237_p29
  have hstep := st237_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p31 : ((257973766867/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT237 (i+1))
      = (∑ i ∈ Finset.range 30, stT237 (i+1)) + stT237 31 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 30
    simpa using h
  have hprev := st237_p30
  have hstep := st237_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p32 : ((75073521979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT237 (i+1))
      = (∑ i ∈ Finset.range 31, stT237 (i+1)) + stT237 32 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 31
    simpa using h
  have hprev := st237_p31
  have hstep := st237_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p33 : ((314658698829/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT237 (i+1))
      = (∑ i ∈ Finset.range 32, stT237 (i+1)) + stT237 33 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 32
    simpa using h
  have hprev := st237_p32
  have hstep := st237_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p34 : ((2940776117581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT237 (i+1))
      = (∑ i ∈ Finset.range 33, stT237 (i+1)) + stT237 34 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 33
    simpa using h
  have hprev := st237_p33
  have hstep := st237_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p35 : ((4503374586949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT237 (i+1))
      = (∑ i ∈ Finset.range 34, stT237 (i+1)) + stT237 35 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 34
    simpa using h
  have hprev := st237_p34
  have hstep := st237_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p36 : ((5682974115109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT237 (i+1))
      = (∑ i ∈ Finset.range 35, stT237 (i+1)) + stT237 36 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 35
    simpa using h
  have hprev := st237_p35
  have hstep := st237_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p37 : ((3289175676051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT237 (i+1))
      = (∑ i ∈ Finset.range 36, stT237 (i+1)) + stT237 37 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 36
    simpa using h
  have hprev := st237_p36
  have hstep := st237_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p38 : ((1852672877787/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT237 (i+1))
      = (∑ i ∈ Finset.range 37, stT237 (i+1)) + stT237 38 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 37
    simpa using h
  have hprev := st237_p37
  have hstep := st237_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p39 : ((839974193617/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT237 (i+1))
      = (∑ i ∈ Finset.range 38, stT237 (i+1)) + stT237 39 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 38
    simpa using h
  have hprev := st237_p38
  have hstep := st237_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p40 : ((4842292080899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT237 (i+1))
      = (∑ i ∈ Finset.range 39, stT237 (i+1)) + stT237 40 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 39
    simpa using h
  have hprev := st237_p39
  have hstep := st237_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p41 : ((11217824146759/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT237 (i+1))
      = (∑ i ∈ Finset.range 40, stT237 (i+1)) + stT237 41 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 40
    simpa using h
  have hprev := st237_p40
  have hstep := st237_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p42 : ((12650138356877/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT237 (i+1))
      = (∑ i ∈ Finset.range 41, stT237 (i+1)) + stT237 42 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 41
    simpa using h
  have hprev := st237_p41
  have hstep := st237_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p43 : ((3339697815363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT237 (i+1))
      = (∑ i ∈ Finset.range 42, stT237 (i+1)) + stT237 43 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 42
    simpa using h
  have hprev := st237_p42
  have hstep := st237_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p44 : ((12839897679837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT237 (i+1))
      = (∑ i ∈ Finset.range 43, stT237 (i+1)) + stT237 44 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 43
    simpa using h
  have hprev := st237_p43
  have hstep := st237_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p45 : ((11400112873893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT237 (i+1))
      = (∑ i ∈ Finset.range 44, stT237 (i+1)) + stT237 45 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 44
    simpa using h
  have hprev := st237_p44
  have hstep := st237_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p46 : ((10385405234533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT237 (i+1))
      = (∑ i ∈ Finset.range 45, stT237 (i+1)) + stT237 46 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 45
    simpa using h
  have hprev := st237_p45
  have hstep := st237_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p47 : ((1373718174371/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT237 (i+1))
      = (∑ i ∈ Finset.range 46, stT237 (i+1)) + stT237 47 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 46
    simpa using h
  have hprev := st237_p46
  have hstep := st237_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p48 : ((3104211224617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT237 (i+1))
      = (∑ i ∈ Finset.range 47, stT237 (i+1)) + stT237 48 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 47
    simpa using h
  have hprev := st237_p47
  have hstep := st237_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p49 : ((12451603459469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT237 (i+1))
      = (∑ i ∈ Finset.range 48, stT237 (i+1)) + stT237 49 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 48
    simpa using h
  have hprev := st237_p48
  have hstep := st237_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p50 : ((11044392647197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT237 (i+1))
      = (∑ i ∈ Finset.range 49, stT237 (i+1)) + stT237 50 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 49
    simpa using h
  have hprev := st237_p49
  have hstep := st237_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p51 : ((1093118412919/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT237 (i+1))
      = (∑ i ∈ Finset.range 50, stT237 (i+1)) + stT237 51 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 50
    simpa using h
  have hprev := st237_p50
  have hstep := st237_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p52 : ((615863216447/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT237 (i+1))
      = (∑ i ∈ Finset.range 51, stT237 (i+1)) + stT237 52 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 51
    simpa using h
  have hprev := st237_p51
  have hstep := st237_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p53 : ((1200755051609/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT237 (i+1))
      = (∑ i ∈ Finset.range 52, stT237 (i+1)) + stT237 53 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 52
    simpa using h
  have hprev := st237_p52
  have hstep := st237_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p54 : ((5409827588751/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT237 (i+1))
      = (∑ i ∈ Finset.range 53, stT237 (i+1)) + stT237 54 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 53
    simpa using h
  have hprev := st237_p53
  have hstep := st237_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p55 : ((11853153120239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT237 (i+1))
      = (∑ i ∈ Finset.range 54, stT237 (i+1)) + stT237 55 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 54
    simpa using h
  have hprev := st237_p54
  have hstep := st237_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p56 : ((487627145041/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT237 (i+1))
      = (∑ i ∈ Finset.range 55, stT237 (i+1)) + stT237 56 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 55
    simpa using h
  have hprev := st237_p55
  have hstep := st237_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p57 : ((10911343990117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT237 (i+1))
      = (∑ i ∈ Finset.range 56, stT237 (i+1)) + stT237 57 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 56
    simpa using h
  have hprev := st237_p56
  have hstep := st237_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p58 : ((11900108756461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT237 (i+1))
      = (∑ i ∈ Finset.range 57, stT237 (i+1)) + stT237 58 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 57
    simpa using h
  have hprev := st237_p57
  have hstep := st237_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p59 : ((11974292995459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT237 (i+1))
      = (∑ i ∈ Finset.range 58, stT237 (i+1)) + stT237 59 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 58
    simpa using h
  have hprev := st237_p58
  have hstep := st237_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p60 : ((1370494877183/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT237 (i+1))
      = (∑ i ∈ Finset.range 59, stT237 (i+1)) + stT237 60 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 59
    simpa using h
  have hprev := st237_p59
  have hstep := st237_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p61 : ((305934269453/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT237 (i+1))
      = (∑ i ∈ Finset.range 60, stT237 (i+1)) + stT237 61 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 60
    simpa using h
  have hprev := st237_p60
  have hstep := st237_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p62 : ((1420891865959/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT237 (i+1))
      = (∑ i ∈ Finset.range 61, stT237 (i+1)) + stT237 62 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 61
    simpa using h
  have hprev := st237_p61
  have hstep := st237_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p63 : ((11498289799653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT237 (i+1))
      = (∑ i ∈ Finset.range 62, stT237 (i+1)) + stT237 63 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 62
    simpa using h
  have hprev := st237_p62
  have hstep := st237_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p64 : ((12082551049653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT237 (i+1))
      = (∑ i ∈ Finset.range 63, stT237 (i+1)) + stT237 64 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 63
    simpa using h
  have hprev := st237_p63
  have hstep := st237_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p65 : ((11026022623253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT237 (i+1))
      = (∑ i ∈ Finset.range 64, stT237 (i+1)) + stT237 65 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 64
    simpa using h
  have hprev := st237_p64
  have hstep := st237_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p66 : ((2450688904047/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT237 (i+1))
      = (∑ i ∈ Finset.range 65, stT237 (i+1)) + stT237 66 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 65
    simpa using h
  have hprev := st237_p65
  have hstep := st237_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p67 : ((2220960398891/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT237 (i+1))
      = (∑ i ∈ Finset.range 66, stT237 (i+1)) + stT237 67 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 66
    simpa using h
  have hprev := st237_p66
  have hstep := st237_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p68 : ((12018594885829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT237 (i+1))
      = (∑ i ∈ Finset.range 67, stT237 (i+1)) + stT237 68 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 67
    simpa using h
  have hprev := st237_p67
  have hstep := st237_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p69 : ((712786240333/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT237 (i+1))
      = (∑ i ∈ Finset.range 68, stT237 (i+1)) + stT237 69 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 68
    simpa using h
  have hprev := st237_p68
  have hstep := st237_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p70 : ((2929864171447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT237 (i+1))
      = (∑ i ∈ Finset.range 69, stT237 (i+1)) + stT237 70 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 69
    simpa using h
  have hprev := st237_p69
  have hstep := st237_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p71 : ((1166424877393/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT237 (i+1))
      = (∑ i ∈ Finset.range 70, stT237 (i+1)) + stT237 71 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 70
    simpa using h
  have hprev := st237_p70
  have hstep := st237_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p72 : ((5757650678149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT237 (i+1))
      = (∑ i ∈ Finset.range 71, stT237 (i+1)) + stT237 72 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 71
    simpa using h
  have hprev := st237_p71
  have hstep := st237_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p73 : ((11809447878407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT237 (i+1))
      = (∑ i ∈ Finset.range 72, stT237 (i+1)) + stT237 73 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 72
    simpa using h
  have hprev := st237_p72
  have hstep := st237_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p74 : ((2856244011953/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT237 (i+1))
      = (∑ i ∈ Finset.range 73, stT237 (i+1)) + stT237 74 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 73
    simpa using h
  have hprev := st237_p73
  have hstep := st237_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p75 : ((2962422718403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT237 (i+1))
      = (∑ i ∈ Finset.range 74, stT237 (i+1)) + stT237 75 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 74
    simpa using h
  have hprev := st237_p74
  have hstep := st237_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p76 : ((5715155954369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT237 (i+1))
      = (∑ i ∈ Finset.range 75, stT237 (i+1)) + stT237 76 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 75
    simpa using h
  have hprev := st237_p75
  have hstep := st237_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p77 : ((11800317720533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT237 (i+1))
      = (∑ i ∈ Finset.range 76, stT237 (i+1)) + stT237 77 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 76
    simpa using h
  have hprev := st237_p76
  have hstep := st237_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p78 : ((11523160976249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT237 (i+1))
      = (∑ i ∈ Finset.range 77, stT237 (i+1)) + stT237 78 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 77
    simpa using h
  have hprev := st237_p77
  have hstep := st237_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p79 : ((11663139800441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT237 (i+1))
      = (∑ i ∈ Finset.range 78, stT237 (i+1)) + stT237 79 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 78
    simpa using h
  have hprev := st237_p78
  have hstep := st237_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p80 : ((11702908234251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT237 (i+1))
      = (∑ i ∈ Finset.range 79, stT237 (i+1)) + stT237 80 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 79
    simpa using h
  have hprev := st237_p79
  have hstep := st237_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p81 : ((2289240939111/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT237 (i+1))
      = (∑ i ∈ Finset.range 80, stT237 (i+1)) + stT237 81 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 80
    simpa using h
  have hprev := st237_p80
  have hstep := st237_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p82 : ((2388598810017/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT237 (i+1))
      = (∑ i ∈ Finset.range 81, stT237 (i+1)) + stT237 82 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 81
    simpa using h
  have hprev := st237_p81
  have hstep := st237_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p83 : ((1400809586841/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT237 (i+1))
      = (∑ i ∈ Finset.range 82, stT237 (i+1)) + stT237 83 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 82
    simpa using h
  have hprev := st237_p82
  have hstep := st237_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p84 : ((1518335147387/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT237 (i+1))
      = (∑ i ∈ Finset.range 83, stT237 (i+1)) + stT237 84 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 83
    simpa using h
  have hprev := st237_p83
  have hstep := st237_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p85 : ((554129009207/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT237 (i+1))
      = (∑ i ∈ Finset.range 84, stT237 (i+1)) + stT237 85 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 84
    simpa using h
  have hprev := st237_p84
  have hstep := st237_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p86 : ((15180618809/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT237 (i+1))
      = (∑ i ∈ Finset.range 85, stT237 (i+1)) + stT237 86 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 85
    simpa using h
  have hprev := st237_p85
  have hstep := st237_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p87 : ((11245353542281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT237 (i+1))
      = (∑ i ∈ Finset.range 86, stT237 (i+1)) + stT237 87 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 86
    simpa using h
  have hprev := st237_p86
  have hstep := st237_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p88 : ((11813117400111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT237 (i+1))
      = (∑ i ∈ Finset.range 87, stT237 (i+1)) + stT237 88 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 87
    simpa using h
  have hprev := st237_p87
  have hstep := st237_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p89 : ((2341842855231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT237 (i+1))
      = (∑ i ∈ Finset.range 88, stT237 (i+1)) + stT237 89 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 88
    simpa using h
  have hprev := st237_p88
  have hstep := st237_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p90 : ((2825789406197/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT237 (i+1))
      = (∑ i ∈ Finset.range 89, stT237 (i+1)) + stT237 90 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 89
    simpa using h
  have hprev := st237_p89
  have hstep := st237_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p91 : ((758497338377/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT237 (i+1))
      = (∑ i ∈ Finset.range 90, stT237 (i+1)) + stT237 91 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 90
    simpa using h
  have hprev := st237_p90
  have hstep := st237_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p92 : ((2774667043499/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT237 (i+1))
      = (∑ i ∈ Finset.range 91, stT237 (i+1)) + stT237 92 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 91
    simpa using h
  have hprev := st237_p91
  have hstep := st237_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p93 : ((480770059833/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT237 (i+1))
      = (∑ i ∈ Finset.range 92, stT237 (i+1)) + stT237 93 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 92
    simpa using h
  have hprev := st237_p92
  have hstep := st237_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p94 : ((11537612490173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT237 (i+1))
      = (∑ i ∈ Finset.range 93, stT237 (i+1)) + stT237 94 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 93
    simpa using h
  have hprev := st237_p93
  have hstep := st237_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p95 : ((569321878123/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT237 (i+1))
      = (∑ i ∈ Finset.range 94, stT237 (i+1)) + stT237 95 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 94
    simpa using h
  have hprev := st237_p94
  have hstep := st237_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p96 : ((606200450893/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT237 (i+1))
      = (∑ i ∈ Finset.range 95, stT237 (i+1)) + stT237 96 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 95
    simpa using h
  have hprev := st237_p95
  have hstep := st237_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p97 : ((694478453801/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT237 (i+1))
      = (∑ i ∈ Finset.range 96, stT237 (i+1)) + stT237 97 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 96
    simpa using h
  have hprev := st237_p96
  have hstep := st237_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p98 : ((1490730100409/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT237 (i+1))
      = (∑ i ∈ Finset.range 97, stT237 (i+1)) + stT237 98 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 97
    simpa using h
  have hprev := st237_p97
  have hstep := st237_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p99 : ((2931042972067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT237 (i+1))
      = (∑ i ∈ Finset.range 98, stT237 (i+1)) + stT237 99 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 98
    simpa using h
  have hprev := st237_p98
  have hstep := st237_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p100 : ((2798722722067/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT237 (i+1))
      = (∑ i ∈ Finset.range 99, stT237 (i+1)) + stT237 100 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 99
    simpa using h
  have hprev := st237_p99
  have hstep := st237_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p101 : ((3040932638533/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT237 (i+1))
      = (∑ i ∈ Finset.range 100, stT237 (i+1)) + stT237 101 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 100
    simpa using h
  have hprev := st237_p100
  have hstep := st237_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p102 : ((283343747119/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT237 (i+1))
      = (∑ i ∈ Finset.range 101, stT237 (i+1)) + stT237 102 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 101
    simpa using h
  have hprev := st237_p101
  have hstep := st237_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p103 : ((2299022457689/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT237 (i+1))
      = (∑ i ∈ Finset.range 102, stT237 (i+1)) + stT237 103 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 102
    simpa using h
  have hprev := st237_p102
  have hstep := st237_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p104 : ((2423418640373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT237 (i+1))
      = (∑ i ∈ Finset.range 103, stT237 (i+1)) + stT237 104 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 103
    simpa using h
  have hprev := st237_p103
  have hstep := st237_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p105 : ((2228238440373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT237 (i+1))
      = (∑ i ∈ Finset.range 104, stT237 (i+1)) + stT237 105 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 104
    simpa using h
  have hprev := st237_p104
  have hstep := st237_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p106 : ((2351229928839/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT237 (i+1))
      = (∑ i ∈ Finset.range 105, stT237 (i+1)) + stT237 106 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 105
    simpa using h
  have hprev := st237_p105
  have hstep := st237_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p107 : ((11977008217283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT237 (i+1))
      = (∑ i ∈ Finset.range 106, stT237 (i+1)) + stT237 107 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 106
    simpa using h
  have hprev := st237_p106
  have hstep := st237_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p108 : ((11091920124973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT237 (i+1))
      = (∑ i ∈ Finset.range 107, stT237 (i+1)) + stT237 108 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 107
    simpa using h
  have hprev := st237_p107
  have hstep := st237_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p109 : ((11906467807111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT237 (i+1))
      = (∑ i ∈ Finset.range 108, stT237 (i+1)) + stT237 109 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 108
    simpa using h
  have hprev := st237_p108
  have hstep := st237_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p110 : ((5934300512033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT237 (i+1))
      = (∑ i ∈ Finset.range 109, stT237 (i+1)) + stT237 110 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 109
    simpa using h
  have hprev := st237_p109
  have hstep := st237_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p111 : ((5546298959003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT237 (i+1))
      = (∑ i ∈ Finset.range 110, stT237 (i+1)) + stT237 111 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 110
    simpa using h
  have hprev := st237_p110
  have hstep := st237_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p112 : ((11962011474017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT237 (i+1))
      = (∑ i ∈ Finset.range 111, stT237 (i+1)) + stT237 112 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 111
    simpa using h
  have hprev := st237_p111
  have hstep := st237_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p113 : ((11836688622397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT237 (i+1))
      = (∑ i ∈ Finset.range 112, stT237 (i+1)) + stT237 113 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 112
    simpa using h
  have hprev := st237_p112
  have hstep := st237_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p114 : ((11091541737383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT237 (i+1))
      = (∑ i ∈ Finset.range 113, stT237 (i+1)) + stT237 114 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 113
    simpa using h
  have hprev := st237_p113
  have hstep := st237_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p115 : ((2388528187139/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT237 (i+1))
      = (∑ i ∈ Finset.range 114, stT237 (i+1)) + stT237 115 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 114
    simpa using h
  have hprev := st237_p114
  have hstep := st237_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p116 : ((5943307852519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT237 (i+1))
      = (∑ i ∈ Finset.range 115, stT237 (i+1)) + stT237 116 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 115
    simpa using h
  have hprev := st237_p115
  have hstep := st237_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p117 : ((11086063478609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT237 (i+1))
      = (∑ i ∈ Finset.range 116, stT237 (i+1)) + stT237 117 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 116
    simpa using h
  have hprev := st237_p116
  have hstep := st237_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p118 : ((11845454176949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT237 (i+1))
      = (∑ i ∈ Finset.range 117, stT237 (i+1)) + stT237 118 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 117
    simpa using h
  have hprev := st237_p117
  have hstep := st237_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p119 : ((2400364354339/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT237 (i+1))
      = (∑ i ∈ Finset.range 118, stT237 (i+1)) + stT237 119 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 118
    simpa using h
  have hprev := st237_p118
  have hstep := st237_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p120 : ((11115292577271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT237 (i+1))
      = (∑ i ∈ Finset.range 119, stT237 (i+1)) + stT237 120 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 119
    simpa using h
  have hprev := st237_p119
  have hstep := st237_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p121 : ((11655993854751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT237 (i+1))
      = (∑ i ∈ Finset.range 120, stT237 (i+1)) + stT237 121 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 120
    simpa using h
  have hprev := st237_p120
  have hstep := st237_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p122 : ((6066094501413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT237 (i+1))
      = (∑ i ∈ Finset.range 121, stT237 (i+1)) + stT237 122 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 121
    simpa using h
  have hprev := st237_p121
  have hstep := st237_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p123 : ((5623351087993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT237 (i+1))
      = (∑ i ∈ Finset.range 122, stT237 (i+1)) + stT237 123 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 122
    simpa using h
  have hprev := st237_p122
  have hstep := st237_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p124 : ((2847039134357/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT237 (i+1))
      = (∑ i ∈ Finset.range 123, stT237 (i+1)) + stT237 124 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 123
    simpa using h
  have hprev := st237_p123
  have hstep := st237_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p125 : ((12176847060769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT237 (i+1))
      = (∑ i ∈ Finset.range 124, stT237 (i+1)) + stT237 125 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 124
    simpa using h
  have hprev := st237_p124
  have hstep := st237_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p126 : ((11532337527109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT237 (i+1))
      = (∑ i ∈ Finset.range 125, stT237 (i+1)) + stT237 126 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 125
    simpa using h
  have hprev := st237_p125
  have hstep := st237_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p127 : ((2784716199703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT237 (i+1))
      = (∑ i ∈ Finset.range 126, stT237 (i+1)) + stT237 127 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 126
    simpa using h
  have hprev := st237_p126
  have hstep := st237_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p128 : ((3002441331327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT237 (i+1))
      = (∑ i ∈ Finset.range 127, stT237 (i+1)) + stT237 128 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 127
    simpa using h
  have hprev := st237_p127
  have hstep := st237_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p129 : ((2383966683763/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT237 (i+1))
      = (∑ i ∈ Finset.range 128, stT237 (i+1)) + stT237 129 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 128
    simpa using h
  have hprev := st237_p128
  have hstep := st237_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p130 : ((11099444709041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT237 (i+1))
      = (∑ i ∈ Finset.range 129, stT237 (i+1)) + stT237 130 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 129
    simpa using h
  have hprev := st237_p129
  have hstep := st237_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p131 : ((11597695383937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT237 (i+1))
      = (∑ i ∈ Finset.range 130, stT237 (i+1)) + stT237 131 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 130
    simpa using h
  have hprev := st237_p130
  have hstep := st237_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p132 : ((12179643763841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT237 (i+1))
      = (∑ i ∈ Finset.range 131, stT237 (i+1)) + stT237 132 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 131
    simpa using h
  have hprev := st237_p131
  have hstep := st237_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p133 : ((11424752538711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT237 (i+1))
      = (∑ i ∈ Finset.range 132, stT237 (i+1)) + stT237 133 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 132
    simpa using h
  have hprev := st237_p132
  have hstep := st237_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p134 : ((11161158463003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT237 (i+1))
      = (∑ i ∈ Finset.range 133, stT237 (i+1)) + stT237 134 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 133
    simpa using h
  have hprev := st237_p133
  have hstep := st237_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p135 : ((12015717508761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT237 (i+1))
      = (∑ i ∈ Finset.range 134, stT237 (i+1)) + stT237 135 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 134
    simpa using h
  have hprev := st237_p134
  have hstep := st237_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p136 : ((11964641795709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT237 (i+1))
      = (∑ i ∈ Finset.range 135, stT237 (i+1)) + stT237 136 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 135
    simpa using h
  have hprev := st237_p135
  have hstep := st237_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p137 : ((11131783714779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT237 (i+1))
      = (∑ i ∈ Finset.range 136, stT237 (i+1)) + stT237 137 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 136
    simpa using h
  have hprev := st237_p136
  have hstep := st237_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p138 : ((11445806945643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT237 (i+1))
      = (∑ i ∈ Finset.range 137, stT237 (i+1)) + stT237 138 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 137
    simpa using h
  have hprev := st237_p137
  have hstep := st237_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p139 : ((2436511831603/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT237 (i+1))
      = (∑ i ∈ Finset.range 138, stT237 (i+1)) + stT237 139 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 138
    simpa using h
  have hprev := st237_p138
  have hstep := st237_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p140 : ((1167344877303/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT237 (i+1))
      = (∑ i ∈ Finset.range 139, stT237 (i+1)) + stT237 140 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 139
    simpa using h
  have hprev := st237_p139
  have hstep := st237_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p141 : ((5532204749771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT237 (i+1))
      = (∑ i ∈ Finset.range 140, stT237 (i+1)) + stT237 141 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 140
    simpa using h
  have hprev := st237_p140
  have hstep := st237_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p142 : ((11703925003393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT237 (i+1))
      = (∑ i ∈ Finset.range 141, stT237 (i+1)) + stT237 142 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 141
    simpa using h
  have hprev := st237_p141
  have hstep := st237_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p143 : ((12184198853801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT237 (i+1))
      = (∑ i ∈ Finset.range 142, stT237 (i+1)) + stT237 143 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 142
    simpa using h
  have hprev := st237_p142
  have hstep := st237_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p144 : ((11465604945593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT237 (i+1))
      = (∑ i ∈ Finset.range 143, stT237 (i+1)) + stT237 144 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 143
    simpa using h
  have hprev := st237_p143
  have hstep := st237_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p145 : ((11095609007623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT237 (i+1))
      = (∑ i ∈ Finset.range 144, stT237 (i+1)) + stT237 145 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 144
    simpa using h
  have hprev := st237_p144
  have hstep := st237_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p146 : ((11856666289573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT237 (i+1))
      = (∑ i ∈ Finset.range 145, stT237 (i+1)) + stT237 146 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 145
    simpa using h
  have hprev := st237_p145
  have hstep := st237_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p147 : ((12144620526609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT237 (i+1))
      = (∑ i ∈ Finset.range 146, stT237 (i+1)) + stT237 147 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 146
    simpa using h
  have hprev := st237_p146
  have hstep := st237_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p148 : ((5682246920967/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT237 (i+1))
      = (∑ i ∈ Finset.range 147, stT237 (i+1)) + stT237 148 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 147
    simpa using h
  have hprev := st237_p147
  have hstep := st237_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p149 : ((5562933562871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT237 (i+1))
      = (∑ i ∈ Finset.range 148, stT237 (i+1)) + stT237 149 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 148
    simpa using h
  have hprev := st237_p148
  have hstep := st237_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p150 : ((5955144356687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT237 (i+1))
      = (∑ i ∈ Finset.range 149, stT237 (i+1)) + stT237 150 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 149
    simpa using h
  have hprev := st237_p149
  have hstep := st237_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p151 : ((6066424169171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT237 (i+1))
      = (∑ i ∈ Finset.range 150, stT237 (i+1)) + stT237 151 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 150
    simpa using h
  have hprev := st237_p150
  have hstep := st237_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p152 : ((5677038390489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT237 (i+1))
      = (∑ i ∈ Finset.range 151, stT237 (i+1)) + stT237 152 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 151
    simpa using h
  have hprev := st237_p151
  have hstep := st237_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p153 : ((5557487594661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT237 (i+1))
      = (∑ i ∈ Finset.range 152, stT237 (i+1)) + stT237 153 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 152
    simpa using h
  have hprev := st237_p152
  have hstep := st237_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p154 : ((593902779231/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT237 (i+1))
      = (∑ i ∈ Finset.range 153, stT237 (i+1)) + stT237 154 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 153
    simpa using h
  have hprev := st237_p153
  have hstep := st237_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p155 : ((12163835282287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT237 (i+1))
      = (∑ i ∈ Finset.range 154, stT237 (i+1)) + stT237 155 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 154
    simpa using h
  have hprev := st237_p154
  have hstep := st237_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p156 : ((11429666700671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT237 (i+1))
      = (∑ i ∈ Finset.range 155, stT237 (i+1)) + stT237 156 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 155
    simpa using h
  have hprev := st237_p155
  have hstep := st237_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p157 : ((553519474081/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT237 (i+1))
      = (∑ i ∈ Finset.range 156, stT237 (i+1)) + stT237 157 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 156
    simpa using h
  have hprev := st237_p156
  have hstep := st237_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p158 : ((1469447158487/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT237 (i+1))
      = (∑ i ∈ Finset.range 157, stT237 (i+1)) + stT237 158 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 157
    simpa using h
  have hprev := st237_p157
  have hstep := st237_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p159 : ((6104422783473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT237 (i+1))
      = (∑ i ∈ Finset.range 158, stT237 (i+1)) + stT237 159 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 158
    simpa using h
  have hprev := st237_p158
  have hstep := st237_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p160 : ((5800386954013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT237 (i+1))
      = (∑ i ∈ Finset.range 159, stT237 (i+1)) + stT237 160 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 159
    simpa using h
  have hprev := st237_p159
  have hstep := st237_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p161 : ((2760568185747/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT237 (i+1))
      = (∑ i ∈ Finset.range 160, stT237 (i+1)) + stT237 161 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 160
    simpa using h
  have hprev := st237_p160
  have hstep := st237_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p162 : ((576812399283/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT237 (i+1))
      = (∑ i ∈ Finset.range 161, stT237 (i+1)) + stT237 162 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 161
    simpa using h
  have hprev := st237_p161
  have hstep := st237_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p163 : ((609831194539/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT237 (i+1))
      = (∑ i ∈ Finset.range 162, stT237 (i+1)) + stT237 163 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 162
    simpa using h
  have hprev := st237_p162
  have hstep := st237_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p164 : ((741216657557/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT237 (i+1))
      = (∑ i ∈ Finset.range 163, stT237 (i+1)) + stT237 164 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 163
    simpa using h
  have hprev := st237_p163
  have hstep := st237_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p165 : ((5559777301173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT237 (i+1))
      = (∑ i ∈ Finset.range 164, stT237 (i+1)) + stT237 165 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 164
    simpa using h
  have hprev := st237_p164
  have hstep := st237_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p166 : ((2814150822149/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT237 (i+1))
      = (∑ i ∈ Finset.range 165, stT237 (i+1)) + stT237 166 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 165
    simpa using h
  have hprev := st237_p165
  have hstep := st237_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p167 : ((6015017367079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT237 (i+1))
      = (∑ i ∈ Finset.range 166, stT237 (i+1)) + stT237 167 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 166
    simpa using h
  have hprev := st237_p166
  have hstep := st237_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p168 : ((6063351301447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT237 (i+1))
      = (∑ i ∈ Finset.range 167, stT237 (i+1)) + stT237 168 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 167
    simpa using h
  have hprev := st237_p167
  have hstep := st237_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p169 : ((11389536997129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT237 (i+1))
      = (∑ i ∈ Finset.range 168, stT237 (i+1)) + stT237 169 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 168
    simpa using h
  have hprev := st237_p168
  have hstep := st237_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p170 : ((11047294205179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT237 (i+1))
      = (∑ i ∈ Finset.range 169, stT237 (i+1)) + stT237 170 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 169
    simpa using h
  have hprev := st237_p169
  have hstep := st237_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p171 : ((2331828257753/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT237 (i+1))
      = (∑ i ∈ Finset.range 170, stT237 (i+1)) + stT237 171 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 170
    simpa using h
  have hprev := st237_p170
  have hstep := st237_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p172 : ((12222866111713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT237 (i+1))
      = (∑ i ∈ Finset.range 171, stT237 (i+1)) + stT237 172 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 171
    simpa using h
  have hprev := st237_p171
  have hstep := st237_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p173 : ((11830778258367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT237 (i+1))
      = (∑ i ∈ Finset.range 172, stT237 (i+1)) + stT237 173 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 172
    simpa using h
  have hprev := st237_p172
  have hstep := st237_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p174 : ((88922226859/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT237 (i+1))
      = (∑ i ∈ Finset.range 173, stT237 (i+1)) + stT237 174 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 173
    simpa using h
  have hprev := st237_p173
  have hstep := st237_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p175 : ((11209005114167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT237 (i+1))
      = (∑ i ∈ Finset.range 174, stT237 (i+1)) + stT237 175 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 174
    simpa using h
  have hprev := st237_p174
  have hstep := st237_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p176 : ((11959274277577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT237 (i+1))
      = (∑ i ∈ Finset.range 175, stT237 (i+1)) + stT237 176 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 175
    simpa using h
  have hprev := st237_p175
  have hstep := st237_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p177 : ((2439708097447/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT237 (i+1))
      = (∑ i ∈ Finset.range 176, stT237 (i+1)) + stT237 177 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 176
    simpa using h
  have hprev := st237_p176
  have hstep := st237_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p178 : ((11563298625659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT237 (i+1))
      = (∑ i ∈ Finset.range 177, stT237 (i+1)) + stT237 178 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 177
    simpa using h
  have hprev := st237_p177
  have hstep := st237_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p179 : ((2205141206019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT237 (i+1))
      = (∑ i ∈ Finset.range 178, stT237 (i+1)) + stT237 179 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 178
    simpa using h
  have hprev := st237_p178
  have hstep := st237_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p180 : ((1139451737371/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT237 (i+1))
      = (∑ i ∈ Finset.range 179, stT237 (i+1)) + stT237 180 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 179
    simpa using h
  have hprev := st237_p179
  have hstep := st237_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p181 : ((1514101149179/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT237 (i+1))
      = (∑ i ∈ Finset.range 180, stT237 (i+1)) + stT237 181 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 180
    simpa using h
  have hprev := st237_p180
  have hstep := st237_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p182 : ((1211656139587/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT237 (i+1))
      = (∑ i ∈ Finset.range 181, stT237 (i+1)) + stT237 182 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 181
    simpa using h
  have hprev := st237_p181
  have hstep := st237_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p183 : ((1425691942577/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT237 (i+1))
      = (∑ i ∈ Finset.range 182, stT237 (i+1)) + stT237 183 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 182
    simpa using h
  have hprev := st237_p182
  have hstep := st237_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p184 : ((5508042963933/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT237 (i+1))
      = (∑ i ∈ Finset.range 183, stT237 (i+1)) + stT237 184 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 183
    simpa using h
  have hprev := st237_p183
  have hstep := st237_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p185 : ((1438159316479/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT237 (i+1))
      = (∑ i ∈ Finset.range 184, stT237 (i+1)) + stT237 185 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 184
    simpa using h
  have hprev := st237_p184
  have hstep := st237_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p186 : ((12170224089517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT237 (i+1))
      = (∑ i ∈ Finset.range 185, stT237 (i+1)) + stT237 186 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 185
    simpa using h
  have hprev := st237_p185
  have hstep := st237_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p187 : ((12071854708103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT237 (i+1))
      = (∑ i ∈ Finset.range 186, stT237 (i+1)) + stT237 187 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 186
    simpa using h
  have hprev := st237_p186
  have hstep := st237_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p188 : ((1419155710041/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT237 (i+1))
      = (∑ i ∈ Finset.range 187, stT237 (i+1)) + stT237 188 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 187
    simpa using h
  have hprev := st237_p187
  have hstep := st237_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p189 : ((1101382519431/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT237 (i+1))
      = (∑ i ∈ Finset.range 188, stT237 (i+1)) + stT237 189 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 188
    simpa using h
  have hprev := st237_p188
  have hstep := st237_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p190 : ((1151632977309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT237 (i+1))
      = (∑ i ∈ Finset.range 189, stT237 (i+1)) + stT237 190 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 189
    simpa using h
  have hprev := st237_p189
  have hstep := st237_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p191 : ((1521424563793/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT237 (i+1))
      = (∑ i ∈ Finset.range 190, stT237 (i+1)) + stT237 191 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 190
    simpa using h
  have hprev := st237_p190
  have hstep := st237_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p192 : ((1511934907859/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT237 (i+1))
      = (∑ i ∈ Finset.range 191, stT237 (i+1)) + stT237 192 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 191
    simpa using h
  have hprev := st237_p191
  have hstep := st237_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p193 : ((712205835313/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT237 (i+1))
      = (∑ i ∈ Finset.range 192, stT237 (i+1)) + stT237 193 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 192
    simpa using h
  have hprev := st237_p192
  have hstep := st237_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p194 : ((2750409111327/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT237 (i+1))
      = (∑ i ∈ Finset.range 193, stT237 (i+1)) + stT237 194 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 193
    simpa using h
  have hprev := st237_p193
  have hstep := st237_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p195 : ((1428531237873/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT237 (i+1))
      = (∑ i ∈ Finset.range 194, stT237 (i+1)) + stT237 195 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 194
    simpa using h
  have hprev := st237_p194
  have hstep := st237_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p196 : ((6057368179677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT237 (i+1))
      = (∑ i ∈ Finset.range 195, stT237 (i+1)) + stT237 196 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 195
    simpa using h
  have hprev := st237_p195
  have hstep := st237_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p197 : ((3043788988191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT237 (i+1))
      = (∑ i ∈ Finset.range 196, stT237 (i+1)) + stT237 197 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 196
    simpa using h
  have hprev := st237_p196
  have hstep := st237_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p198 : ((5768493897747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT237 (i+1))
      = (∑ i ∈ Finset.range 197, stT237 (i+1)) + stT237 198 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 197
    simpa using h
  have hprev := st237_p197
  have hstep := st237_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p199 : ((2753152514511/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT237 (i+1))
      = (∑ i ∈ Finset.range 198, stT237 (i+1)) + stT237 199 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 198
    simpa using h
  have hprev := st237_p198
  have hstep := st237_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p200 : ((2814651644649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT237 (i+1))
      = (∑ i ∈ Finset.range 199, stT237 (i+1)) + stT237 200 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 199
    simpa using h
  have hprev := st237_p199
  have hstep := st237_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p201 : ((5981762069763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT237 (i+1))
      = (∑ i ∈ Finset.range 200, stT237 (i+1)) + stT237 201 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 200
    simpa using h
  have hprev := st237_p200
  have hstep := st237_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p202 : ((12255516190929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT237 (i+1))
      = (∑ i ∈ Finset.range 201, stT237 (i+1)) + stT237 202 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 201
    simpa using h
  have hprev := st237_p201
  have hstep := st237_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p203 : ((11780990827807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT237 (i+1))
      = (∑ i ∈ Finset.range 202, stT237 (i+1)) + stT237 203 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 202
    simpa using h
  have hprev := st237_p202
  have hstep := st237_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p204 : ((11120012914783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT237 (i+1))
      = (∑ i ∈ Finset.range 203, stT237 (i+1)) + stT237 204 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 203
    simpa using h
  have hprev := st237_p203
  have hstep := st237_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p205 : ((11067182197081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT237 (i+1))
      = (∑ i ∈ Finset.range 204, stT237 (i+1)) + stT237 205 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 204
    simpa using h
  have hprev := st237_p204
  have hstep := st237_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p206 : ((11680854869219/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT237 (i+1))
      = (∑ i ∈ Finset.range 205, stT237 (i+1)) + stT237 206 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 205
    simpa using h
  have hprev := st237_p205
  have hstep := st237_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p207 : ((2446445482399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT237 (i+1))
      = (∑ i ∈ Finset.range 206, stT237 (i+1)) + stT237 207 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 206
    simpa using h
  have hprev := st237_p206
  have hstep := st237_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p208 : ((12076886226459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT237 (i+1))
      = (∑ i ∈ Finset.range 207, stT237 (i+1)) + stT237 208 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 207
    simpa using h
  have hprev := st237_p207
  have hstep := st237_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p209 : ((11400073534419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT237 (i+1))
      = (∑ i ∈ Finset.range 208, stT237 (i+1)) + stT237 209 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 208
    simpa using h
  have hprev := st237_p208
  have hstep := st237_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p210 : ((2196734919753/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT237 (i+1))
      = (∑ i ∈ Finset.range 209, stT237 (i+1)) + stT237 210 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 209
    simpa using h
  have hprev := st237_p209
  have hstep := st237_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p211 : ((11300426517417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT237 (i+1))
      = (∑ i ∈ Finset.range 210, stT237 (i+1)) + stT237 211 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 210
    simpa using h
  have hprev := st237_p210
  have hstep := st237_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p212 : ((11986926324537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT237 (i+1))
      = (∑ i ∈ Finset.range 211, stT237 (i+1)) + stT237 212 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 211
    simpa using h
  have hprev := st237_p211
  have hstep := st237_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p213 : ((12271006639713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT237 (i+1))
      = (∑ i ∈ Finset.range 212, stT237 (i+1)) + stT237 213 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 212
    simpa using h
  have hprev := st237_p212
  have hstep := st237_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p214 : ((2367959708031/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT237 (i+1))
      = (∑ i ∈ Finset.range 213, stT237 (i+1)) + stT237 214 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 213
    simpa using h
  have hprev := st237_p213
  have hstep := st237_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p215 : ((223474166911/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT237 (i+1))
      = (∑ i ∈ Finset.range 214, stT237 (i+1)) + stT237 215 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 214
    simpa using h
  have hprev := st237_p214
  have hstep := st237_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p216 : ((550121896777/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT237 (i+1))
      = (∑ i ∈ Finset.range 215, stT237 (i+1)) + stT237 216 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 215
    simpa using h
  have hprev := st237_p215
  have hstep := st237_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p217 : ((1438503336377/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT237 (i+1))
      = (∑ i ∈ Finset.range 216, stT237 (i+1)) + stT237 217 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 216
    simpa using h
  have hprev := st237_p216
  have hstep := st237_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p218 : ((6071033521883/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT237 (i+1))
      = (∑ i ∈ Finset.range 217, stT237 (i+1)) + stT237 218 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 217
    simpa using h
  have hprev := st237_p217
  have hstep := st237_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p219 : ((3056902147649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT237 (i+1))
      = (∑ i ∈ Finset.range 218, stT237 (i+1)) + stT237 219 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 218
    simpa using h
  have hprev := st237_p218
  have hstep := st237_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p220 : ((2919524121749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT237 (i+1))
      = (∑ i ∈ Finset.range 219, stT237 (i+1)) + stT237 220 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 219
    simpa using h
  have hprev := st237_p219
  have hstep := st237_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p221 : ((11074356998017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT237 (i+1))
      = (∑ i ∈ Finset.range 220, stT237 (i+1)) + stT237 221 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 220
    simpa using h
  have hprev := st237_p220
  have hstep := st237_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p222 : ((11044771055143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT237 (i+1))
      = (∑ i ∈ Finset.range 221, stT237 (i+1)) + stT237 222 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 221
    simpa using h
  have hprev := st237_p221
  have hstep := st237_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p223 : ((5807872633023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT237 (i+1))
      = (∑ i ∈ Finset.range 222, stT237 (i+1)) + stT237 223 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 222
    simpa using h
  have hprev := st237_p222
  have hstep := st237_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p224 : ((2439719435399/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT237 (i+1))
      = (∑ i ∈ Finset.range 223, stT237 (i+1)) + stT237 224 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 223
    simpa using h
  have hprev := st237_p223
  have hstep := st237_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p225 : ((12201473174119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT237 (i+1))
      = (∑ i ∈ Finset.range 224, stT237 (i+1)) + stT237 225 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 224
    simpa using h
  have hprev := st237_p224
  have hstep := st237_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p226 : ((581277906171/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT237 (i+1))
      = (∑ i ∈ Finset.range 225, stT237 (i+1)) + stT237 226 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 225
    simpa using h
  have hprev := st237_p225
  have hstep := st237_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p227 : ((690641089117/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT237 (i+1))
      = (∑ i ∈ Finset.range 226, stT237 (i+1)) + stT237 227 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 226
    simpa using h
  have hprev := st237_p226
  have hstep := st237_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p228 : ((5522845878587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT237 (i+1))
      = (∑ i ∈ Finset.range 227, stT237 (i+1)) + stT237 228 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 227
    simpa using h
  have hprev := st237_p227
  have hstep := st237_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p229 : ((2903075059751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT237 (i+1))
      = (∑ i ∈ Finset.range 228, stT237 (i+1)) + stT237 229 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 228
    simpa using h
  have hprev := st237_p228
  have hstep := st237_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p230 : ((3048340430031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT237 (i+1))
      = (∑ i ∈ Finset.range 229, stT237 (i+1)) + stT237 230 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 229
    simpa using h
  have hprev := st237_p229
  have hstep := st237_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p231 : ((6113221090251/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT237 (i+1))
      = (∑ i ∈ Finset.range 230, stT237 (i+1)) + stT237 231 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 230
    simpa using h
  have hprev := st237_p230
  have hstep := st237_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p232 : ((11683587212919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT237 (i+1))
      = (∑ i ∈ Finset.range 231, stT237 (i+1)) + stT237 232 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 231
    simpa using h
  have hprev := st237_p231
  have hstep := st237_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p233 : ((11085894517683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT237 (i+1))
      = (∑ i ∈ Finset.range 232, stT237 (i+1)) + stT237 233 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 232
    simpa using h
  have hprev := st237_p232
  have hstep := st237_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p234 : ((2749657815639/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT237 (i+1))
      = (∑ i ∈ Finset.range 233, stT237 (i+1)) + stT237 234 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 233
    simpa using h
  have hprev := st237_p233
  have hstep := st237_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p235 : ((575002583001/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT237 (i+1))
      = (∑ i ∈ Finset.range 234, stT237 (i+1)) + stT237 235 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 234
    simpa using h
  have hprev := st237_p234
  have hstep := st237_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p236 : ((3029864030333/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT237 (i+1))
      = (∑ i ∈ Finset.range 235, stT237 (i+1)) + stT237 236 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 235
    simpa using h
  have hprev := st237_p235
  have hstep := st237_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p237 : ((3071020722173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT237 (i+1))
      = (∑ i ∈ Finset.range 236, stT237 (i+1)) + stT237 237 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 236
    simpa using h
  have hprev := st237_p236
  have hstep := st237_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p238 : ((2961552030653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT237 (i+1))
      = (∑ i ∈ Finset.range 237, stT237 (i+1)) + stT237 238 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 237
    simpa using h
  have hprev := st237_p237
  have hstep := st237_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p239 : ((11208063155303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT237 (i+1))
      = (∑ i ∈ Finset.range 238, stT237 (i+1)) + stT237 239 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 238
    simpa using h
  have hprev := st237_p238
  have hstep := st237_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p240 : ((10946766855899/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT237 (i+1))
      = (∑ i ∈ Finset.range 239, stT237 (i+1)) + stT237 240 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 239
    simpa using h
  have hprev := st237_p239
  have hstep := st237_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p241 : ((11293659677487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT237 (i+1))
      = (∑ i ∈ Finset.range 240, stT237 (i+1)) + stT237 241 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 240
    simpa using h
  have hprev := st237_p240
  have hstep := st237_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p242 : ((11936313971951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT237 (i+1))
      = (∑ i ∈ Finset.range 241, stT237 (i+1)) + stT237 242 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 241
    simpa using h
  have hprev := st237_p241
  have hstep := st237_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p243 : ((12305962309451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT237 (i+1))
      = (∑ i ∈ Finset.range 242, stT237 (i+1)) + stT237 243 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 242
    simpa using h
  have hprev := st237_p242
  have hstep := st237_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p244 : ((3020229999239/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT237 (i+1))
      = (∑ i ∈ Finset.range 243, stT237 (i+1)) + stT237 244 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 243
    simpa using h
  have hprev := st237_p243
  have hstep := st237_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p245 : ((2865169440323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT237 (i+1))
      = (∑ i ∈ Finset.range 244, stT237 (i+1)) + stT237 245 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 244
    simpa using h
  have hprev := st237_p244
  have hstep := st237_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p246 : ((5491299149383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT237 (i+1))
      = (∑ i ∈ Finset.range 245, stT237 (i+1)) + stT237 246 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 245
    simpa using h
  have hprev := st237_p245
  have hstep := st237_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p247 : ((5527384405733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT237 (i+1))
      = (∑ i ∈ Finset.range 246, stT237 (i+1)) + stT237 247 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 246
    simpa using h
  have hprev := st237_p246
  have hstep := st237_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p248 : ((5806076698233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT237 (i+1))
      = (∑ i ∈ Finset.range 247, stT237 (i+1)) + stT237 248 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 247
    simpa using h
  have hprev := st237_p247
  have hstep := st237_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p249 : ((6090795583229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT237 (i+1))
      = (∑ i ∈ Finset.range 248, stT237 (i+1)) + stT237 249 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 248
    simpa using h
  have hprev := st237_p248
  have hstep := st237_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p250 : ((12286481930843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT237 (i+1))
      = (∑ i ∈ Finset.range 249, stT237 (i+1)) + stT237 250 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 249
    simpa using h
  have hprev := st237_p249
  have hstep := st237_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p251 : ((740174791293/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT237 (i+1))
      = (∑ i ∈ Finset.range 250, stT237 (i+1)) + stT237 251 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 250
    simpa using h
  have hprev := st237_p250
  have hstep := st237_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p252 : ((11219989742513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT237 (i+1))
      = (∑ i ∈ Finset.range 251, stT237 (i+1)) + stT237 252 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 251
    simpa using h
  have hprev := st237_p251
  have hstep := st237_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p253 : ((10928968084403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT237 (i+1))
      = (∑ i ∈ Finset.range 252, stT237 (i+1)) + stT237 253 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 252
    simpa using h
  have hprev := st237_p252
  have hstep := st237_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p254 : ((2800988343857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT237 (i+1))
      = (∑ i ∈ Finset.range 253, stT237 (i+1)) + stT237 254 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 253
    simpa using h
  have hprev := st237_p253
  have hstep := st237_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p255 : ((2954840778293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT237 (i+1))
      = (∑ i ∈ Finset.range 254, stT237 (i+1)) + stT237 255 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 254
    simpa using h
  have hprev := st237_p254
  have hstep := st237_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p256 : ((3070033590793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT237 (i+1))
      = (∑ i ∈ Finset.range 255, stT237 (i+1)) + stT237 256 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 255
    simpa using h
  have hprev := st237_p255
  have hstep := st237_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p257 : ((244419570523/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT237 (i+1))
      = (∑ i ∈ Finset.range 256, stT237 (i+1)) + stT237 257 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 256
    simpa using h
  have hprev := st237_p256
  have hstep := st237_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p258 : ((11691980115769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT237 (i+1))
      = (∑ i ∈ Finset.range 257, stT237 (i+1)) + stT237 258 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 257
    simpa using h
  have hprev := st237_p257
  have hstep := st237_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p259 : ((11110707743239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT237 (i+1))
      = (∑ i ∈ Finset.range 258, stT237 (i+1)) + stT237 259 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 258
    simpa using h
  have hprev := st237_p258
  have hstep := st237_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p260 : ((10929691356119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT237 (i+1))
      = (∑ i ∈ Finset.range 259, stT237 (i+1)) + stT237 260 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 259
    simpa using h
  have hprev := st237_p259
  have hstep := st237_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p261 : ((11286109152143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT237 (i+1))
      = (∑ i ∈ Finset.range 260, stT237 (i+1)) + stT237 261 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 260
    simpa using h
  have hprev := st237_p260
  have hstep := st237_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p262 : ((11903082679661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT237 (i+1))
      = (∑ i ∈ Finset.range 261, stT237 (i+1)) + stT237 262 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 261
    simpa using h
  have hprev := st237_p261
  have hstep := st237_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p263 : ((12309076637573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT237 (i+1))
      = (∑ i ∈ Finset.range 262, stT237 (i+1)) + stT237 263 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 262
    simpa using h
  have hprev := st237_p262
  have hstep := st237_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p264 : ((12198457909401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT237 (i+1))
      = (∑ i ∈ Finset.range 263, stT237 (i+1)) + stT237 264 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 263
    simpa using h
  have hprev := st237_p263
  have hstep := st237_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p265 : ((11657604681977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT237 (i+1))
      = (∑ i ∈ Finset.range 264, stT237 (i+1)) + stT237 265 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 264
    simpa using h
  have hprev := st237_p264
  have hstep := st237_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p266 : ((11092490711897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT237 (i+1))
      = (∑ i ∈ Finset.range 265, stT237 (i+1)) + stT237 266 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 265
    simpa using h
  have hprev := st237_p265
  have hstep := st237_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p267 : ((2730400351253/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT237 (i+1))
      = (∑ i ∈ Finset.range 266, stT237 (i+1)) + stT237 267 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 266
    simpa using h
  have hprev := st237_p266
  have hstep := st237_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p268 : ((352125245373/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT237 (i+1))
      = (∑ i ∈ Finset.range 267, stT237 (i+1)) + stT237 268 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 267
    simpa using h
  have hprev := st237_p267
  have hstep := st237_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p269 : ((5937741022683/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT237 (i+1))
      = (∑ i ∈ Finset.range 268, stT237 (i+1)) + stT237 269 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 268
    simpa using h
  have hprev := st237_p268
  have hstep := st237_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p270 : ((6150960981453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT237 (i+1))
      = (∑ i ∈ Finset.range 269, stT237 (i+1)) + stT237 270 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 269
    simpa using h
  have hprev := st237_p269
  have hstep := st237_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p271 : ((6120714482509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT237 (i+1))
      = (∑ i ∈ Finset.range 270, stT237 (i+1)) + stT237 271 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 270
    simpa using h
  have hprev := st237_p270
  have hstep := st237_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p272 : ((5870170853299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT237 (i+1))
      = (∑ i ∈ Finset.range 271, stT237 (i+1)) + stT237 272 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 271
    simpa using h
  have hprev := st237_p271
  have hstep := st237_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p273 : ((5578629802173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT237 (i+1))
      = (∑ i ∈ Finset.range 272, stT237 (i+1)) + stT237 273 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 272
    simpa using h
  have hprev := st237_p272
  have hstep := st237_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p274 : ((5451956083287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT237 (i+1))
      = (∑ i ∈ Finset.range 273, stT237 (i+1)) + stT237 274 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 273
    simpa using h
  have hprev := st237_p273
  have hstep := st237_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p275 : ((2788908965297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT237 (i+1))
      = (∑ i ∈ Finset.range 274, stT237 (i+1)) + stT237 275 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 274
    simpa using h
  have hprev := st237_p274
  have hstep := st237_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p276 : ((11734116716993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT237 (i+1))
      = (∑ i ∈ Finset.range 275, stT237 (i+1)) + stT237 276 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 275
    simpa using h
  have hprev := st237_p275
  have hstep := st237_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p277 : ((12237554180801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT237 (i+1))
      = (∑ i ∈ Finset.range 276, stT237 (i+1)) + stT237 277 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 276
    simpa using h
  have hprev := st237_p276
  have hstep := st237_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p278 : ((12320884235441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT237 (i+1))
      = (∑ i ∈ Finset.range 277, stT237 (i+1)) + stT237 278 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 277
    simpa using h
  have hprev := st237_p277
  have hstep := st237_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p279 : ((11929916588301/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT237 (i+1))
      = (∑ i ∈ Finset.range 278, stT237 (i+1)) + stT237 279 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 278
    simpa using h
  have hprev := st237_p278
  have hstep := st237_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p280 : ((11332309954911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT237 (i+1))
      = (∑ i ∈ Finset.range 279, stT237 (i+1)) + stT237 280 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 279
    simpa using h
  have hprev := st237_p279
  have hstep := st237_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p281 : ((10931271462261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT237 (i+1))
      = (∑ i ∈ Finset.range 280, stT237 (i+1)) + stT237 281 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 280
    simpa using h
  have hprev := st237_p280
  have hstep := st237_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p282 : ((5496745074207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT237 (i+1))
      = (∑ i ∈ Finset.range 281, stT237 (i+1)) + stT237 282 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 281
    simpa using h
  have hprev := st237_p281
  have hstep := st237_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p283 : ((5737391409747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT237 (i+1))
      = (∑ i ∈ Finset.range 282, stT237 (i+1)) + stT237 283 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 282
    simpa using h
  have hprev := st237_p282
  have hstep := st237_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p284 : ((376726505997/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT237 (i+1))
      = (∑ i ∈ Finset.range 283, stT237 (i+1)) + stT237 284 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 283
    simpa using h
  have hprev := st237_p283
  have hstep := st237_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p285 : ((3088528307217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT237 (i+1))
      = (∑ i ∈ Finset.range 284, stT237 (i+1)) + stT237 285 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 284
    simpa using h
  have hprev := st237_p284
  have hstep := st237_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p286 : ((12178644052683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT237 (i+1))
      = (∑ i ∈ Finset.range 285, stT237 (i+1)) + stT237 286 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 285
    simpa using h
  have hprev := st237_p285
  have hstep := st237_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p287 : ((11645146000519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT237 (i+1))
      = (∑ i ∈ Finset.range 286, stT237 (i+1)) + stT237 287 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 286
    simpa using h
  have hprev := st237_p286
  have hstep := st237_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p288 : ((443933270127/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT237 (i+1))
      = (∑ i ∈ Finset.range 287, stT237 (i+1)) + stT237 288 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 287
    simpa using h
  have hprev := st237_p287
  have hstep := st237_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p289 : ((10887060323179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT237 (i+1))
      = (∑ i ∈ Finset.range 288, stT237 (i+1)) + stT237 289 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 288
    simpa using h
  have hprev := st237_p288
  have hstep := st237_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p290 : ((11143166930659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT237 (i+1))
      = (∑ i ∈ Finset.range 289, stT237 (i+1)) + stT237 290 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 289
    simpa using h
  have hprev := st237_p289
  have hstep := st237_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p291 : ((11702534960969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT237 (i+1))
      = (∑ i ∈ Finset.range 290, stT237 (i+1)) + stT237 291 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 290
    simpa using h
  have hprev := st237_p290
  have hstep := st237_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p292 : ((12213401369819/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT237 (i+1))
      = (∑ i ∈ Finset.range 291, stT237 (i+1)) + stT237 292 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 291
    simpa using h
  have hprev := st237_p291
  have hstep := st237_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p293 : ((12358532745369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT237 (i+1))
      = (∑ i ∈ Finset.range 292, stT237 (i+1)) + stT237 293 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 292
    simpa using h
  have hprev := st237_p292
  have hstep := st237_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p294 : ((12050501745813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT237 (i+1))
      = (∑ i ∈ Finset.range 293, stT237 (i+1)) + stT237 294 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 293
    simpa using h
  have hprev := st237_p293
  have hstep := st237_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p295 : ((574049986807/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT237 (i+1))
      = (∑ i ∈ Finset.range 294, stT237 (i+1)) + stT237 295 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 294
    simpa using h
  have hprev := st237_p294
  have hstep := st237_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p296 : ((1099876317501/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT237 (i+1))
      = (∑ i ∈ Finset.range 295, stT237 (i+1)) + stT237 296 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 295
    simpa using h
  have hprev := st237_p295
  have hstep := st237_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p297 : ((10895366243541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT237 (i+1))
      = (∑ i ∈ Finset.range 296, stT237 (i+1)) + stT237 297 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 296
    simpa using h
  have hprev := st237_p296
  have hstep := st237_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p298 : ((11230756618157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT237 (i+1))
      = (∑ i ∈ Finset.range 297, stT237 (i+1)) + stT237 298 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 297
    simpa using h
  have hprev := st237_p297
  have hstep := st237_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p299 : ((11801720247217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT237 (i+1))
      = (∑ i ∈ Finset.range 298, stT237 (i+1)) + stT237 299 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 298
    simpa using h
  have hprev := st237_p298
  have hstep := st237_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p300 : ((12267515257567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT237 (i+1))
      = (∑ i ∈ Finset.range 299, stT237 (i+1)) + stT237 300 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 299
    simpa using h
  have hprev := st237_p299
  have hstep := st237_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p301 : ((12353666541697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT237 (i+1))
      = (∑ i ∈ Finset.range 300, stT237 (i+1)) + stT237 301 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 300
    simpa using h
  have hprev := st237_p300
  have hstep := st237_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p302 : ((12011837992873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT237 (i+1))
      = (∑ i ∈ Finset.range 301, stT237 (i+1)) + stT237 302 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 301
    simpa using h
  have hprev := st237_p301
  have hstep := st237_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p303 : ((5721944454359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT237 (i+1))
      = (∑ i ∈ Finset.range 302, stT237 (i+1)) + stT237 303 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 302
    simpa using h
  have hprev := st237_p302
  have hstep := st237_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p304 : ((5490139660259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT237 (i+1))
      = (∑ i ∈ Finset.range 303, stT237 (i+1)) + stT237 304 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 303
    simpa using h
  have hprev := st237_p303
  have hstep := st237_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p305 : ((5443688138983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT237 (i+1))
      = (∑ i ∈ Finset.range 304, stT237 (i+1)) + stT237 305 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 304
    simpa using h
  have hprev := st237_p304
  have hstep := st237_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p306 : ((560809041099/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT237 (i+1))
      = (∑ i ∈ Finset.range 305, stT237 (i+1)) + stT237 306 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 305
    simpa using h
  have hprev := st237_p305
  have hstep := st237_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p307 : ((1177717702183/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT237 (i+1))
      = (∑ i ∈ Finset.range 306, stT237 (i+1)) + stT237 307 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 306
    simpa using h
  have hprev := st237_p306
  have hstep := st237_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p308 : ((6125935545401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT237 (i+1))
      = (∑ i ∈ Finset.range 307, stT237 (i+1)) + stT237 308 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 307
    simpa using h
  have hprev := st237_p307
  have hstep := st237_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p309 : ((6187027853041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT237 (i+1))
      = (∑ i ∈ Finset.range 308, stT237 (i+1)) + stT237 309 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 308
    simpa using h
  have hprev := st237_p308
  have hstep := st237_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p310 : ((3019383668271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT237 (i+1))
      = (∑ i ∈ Finset.range 309, stT237 (i+1)) + stT237 310 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 309
    simpa using h
  have hprev := st237_p309
  have hstep := st237_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p311 : ((2882316116901/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT237 (i+1))
      = (∑ i ∈ Finset.range 310, stT237 (i+1)) + stT237 311 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 310
    simpa using h
  have hprev := st237_p310
  have hstep := st237_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p312 : ((11033097417309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT237 (i+1))
      = (∑ i ∈ Finset.range 311, stT237 (i+1)) + stT237 312 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 311
    simpa using h
  have hprev := st237_p311
  have hstep := st237_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p313 : ((10860725352371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT237 (i+1))
      = (∑ i ∈ Finset.range 312, stT237 (i+1)) + stT237 313 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 312
    simpa using h
  have hprev := st237_p312
  have hstep := st237_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p314 : ((11104199621787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT237 (i+1))
      = (∑ i ∈ Finset.range 313, stT237 (i+1)) + stT237 314 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 313
    simpa using h
  have hprev := st237_p313
  have hstep := st237_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p315 : ((11629260559263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT237 (i+1))
      = (∑ i ∈ Finset.range 314, stT237 (i+1)) + stT237 315 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 314
    simpa using h
  have hprev := st237_p314
  have hstep := st237_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p316 : ((1518952428143/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT237 (i+1))
      = (∑ i ∈ Finset.range 315, stT237 (i+1)) + stT237 316 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 315
    simpa using h
  have hprev := st237_p315
  have hstep := st237_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p317 : ((96810700183/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT237 (i+1))
      = (∑ i ∈ Finset.range 316, stT237 (i+1)) + stT237 317 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 316
    simpa using h
  have hprev := st237_p316
  have hstep := st237_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p318 : ((763972790033/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT237 (i+1))
      = (∑ i ∈ Finset.range 317, stT237 (i+1)) + stT237 318 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 317
    simpa using h
  have hprev := st237_p317
  have hstep := st237_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p319 : ((11738228672087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT237 (i+1))
      = (∑ i ∈ Finset.range 318, stT237 (i+1)) + stT237 319 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 318
    simpa using h
  have hprev := st237_p318
  have hstep := st237_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p320 : ((699538730927/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT237 (i+1))
      = (∑ i ∈ Finset.range 319, stT237 (i+1)) + stT237 320 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 319
    simpa using h
  have hprev := st237_p319
  have hstep := st237_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p321 : ((5436053572531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT237 (i+1))
      = (∑ i ∈ Finset.range 320, stT237 (i+1)) + stT237 321 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 320
    simpa using h
  have hprev := st237_p320
  have hstep := st237_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p322 : ((2735464711483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT237 (i+1))
      = (∑ i ∈ Finset.range 321, stT237 (i+1)) + stT237 322 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 321
    simpa using h
  have hprev := st237_p321
  have hstep := st237_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p323 : ((2840915736349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT237 (i+1))
      = (∑ i ∈ Finset.range 322, stT237 (i+1)) + stT237 323 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 322
    simpa using h
  have hprev := st237_p322
  have hstep := st237_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p324 : ((5959526195003/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT237 (i+1))
      = (∑ i ∈ Finset.range 323, stT237 (i+1)) + stT237 324 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 323
    simpa using h
  have hprev := st237_p323
  have hstep := st237_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p325 : ((6161955639503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT237 (i+1))
      = (∑ i ∈ Finset.range 324, stT237 (i+1)) + stT237 325 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 324
    simpa using h
  have hprev := st237_p324
  have hstep := st237_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p326 : ((6186857199431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT237 (i+1))
      = (∑ i ∈ Finset.range 325, stT237 (i+1)) + stT237 326 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 325
    simpa using h
  have hprev := st237_p325
  have hstep := st237_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p327 : ((1505663371517/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT237 (i+1))
      = (∑ i ∈ Finset.range 326, stT237 (i+1)) + stT237 327 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 326
    simpa using h
  have hprev := st237_p326
  have hstep := st237_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p328 : ((89885973993/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT237 (i+1))
      = (∑ i ∈ Finset.range 327, stT237 (i+1)) + stT237 328 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 327
    simpa using h
  have hprev := st237_p327
  have hstep := st237_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p329 : ((1102425125901/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT237 (i+1))
      = (∑ i ∈ Finset.range 328, stT237 (i+1)) + stT237 329 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 328
    simpa using h
  have hprev := st237_p328
  have hstep := st237_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p330 : ((338747453373/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT237 (i+1))
      = (∑ i ∈ Finset.range 329, stT237 (i+1)) + stT237 330 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 329
    simpa using h
  have hprev := st237_p329
  have hstep := st237_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p331 : ((1104156603797/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT237 (i+1))
      = (∑ i ∈ Finset.range 330, stT237 (i+1)) + stT237 331 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 330
    simpa using h
  have hprev := st237_p330
  have hstep := st237_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p332 : ((2882074180739/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT237 (i+1))
      = (∑ i ∈ Finset.range 331, stT237 (i+1)) + stT237 332 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 331
    simpa using h
  have hprev := st237_p331
  have hstep := st237_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p333 : ((18846105067/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT237 (i+1))
      = (∑ i ∈ Finset.range 332, stT237 (i+1)) + stT237 333 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 332
    simpa using h
  have hprev := st237_p332
  have hstep := st237_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p334 : ((1238275915713/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT237 (i+1))
      = (∑ i ∈ Finset.range 333, stT237 (i+1)) + stT237 334 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 333
    simpa using h
  have hprev := st237_p333
  have hstep := st237_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p335 : ((12338530849721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT237 (i+1))
      = (∑ i ∈ Finset.range 334, stT237 (i+1)) + stT237 335 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 334
    simpa using h
  have hprev := st237_p334
  have hstep := st237_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p336 : ((2987994189199/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT237 (i+1))
      = (∑ i ∈ Finset.range 335, stT237 (i+1)) + stT237 336 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 335
    simpa using h
  have hprev := st237_p335
  have hstep := st237_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p337 : ((1426114670207/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT237 (i+1))
      = (∑ i ∈ Finset.range 336, stT237 (i+1)) + stT237 337 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 336
    simpa using h
  have hprev := st237_p336
  have hstep := st237_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p338 : ((1370898261701/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT237 (i+1))
      = (∑ i ∈ Finset.range 337, stT237 (i+1)) + stT237 338 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 337
    simpa using h
  have hprev := st237_p337
  have hstep := st237_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p339 : ((541704979241/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT237 (i+1))
      = (∑ i ∈ Finset.range 338, stT237 (i+1)) + stT237 339 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 338
    simpa using h
  have hprev := st237_p338
  have hstep := st237_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p340 : ((691890422769/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT237 (i+1))
      = (∑ i ∈ Finset.range 339, stT237 (i+1)) + stT237 340 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 339
    simpa using h
  have hprev := st237_p339
  have hstep := st237_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p341 : ((5781876671187/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT237 (i+1))
      = (∑ i ∈ Finset.range 340, stT237 (i+1)) + stT237 341 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 340
    simpa using h
  have hprev := st237_p340
  have hstep := st237_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p342 : ((1208490148611/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT237 (i+1))
      = (∑ i ∈ Finset.range 341, stT237 (i+1)) + stT237 342 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 341
    simpa using h
  have hprev := st237_p341
  have hstep := st237_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p343 : ((12393759333447/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT237 (i+1))
      = (∑ i ∈ Finset.range 342, stT237 (i+1)) + stT237 343 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 342
    simpa using h
  have hprev := st237_p342
  have hstep := st237_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p344 : ((12350142583339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT237 (i+1))
      = (∑ i ∈ Finset.range 343, stT237 (i+1)) + stT237 344 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 343
    simpa using h
  have hprev := st237_p343
  have hstep := st237_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p345 : ((11975754970831/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT237 (i+1))
      = (∑ i ∈ Finset.range 344, stT237 (i+1)) + stT237 345 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 344
    simpa using h
  have hprev := st237_p344
  have hstep := st237_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p346 : ((11441734101491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT237 (i+1))
      = (∑ i ∈ Finset.range 345, stT237 (i+1)) + stT237 346 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 345
    simpa using h
  have hprev := st237_p345
  have hstep := st237_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p347 : ((2747295337343/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT237 (i+1))
      = (∑ i ∈ Finset.range 346, stT237 (i+1)) + stT237 347 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 346
    simpa using h
  have hprev := st237_p346
  have hstep := st237_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p348 : ((10820148103733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT237 (i+1))
      = (∑ i ∈ Finset.range 347, stT237 (i+1)) + stT237 348 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 347
    simpa using h
  have hprev := st237_p347
  have hstep := st237_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p349 : ((220167003907/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT237 (i+1))
      = (∑ i ∈ Finset.range 348, stT237 (i+1)) + stT237 349 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 348
    simpa using h
  have hprev := st237_p348
  have hstep := st237_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p350 : ((179196872327/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT237 (i+1))
      = (∑ i ∈ Finset.range 349, stT237 (i+1)) + stT237 350 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 349
    simpa using h
  have hprev := st237_p349
  have hstep := st237_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p351 : ((187451545787/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT237 (i+1))
      = (∑ i ∈ Finset.range 350, stT237 (i+1)) + stT237 351 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 350
    simpa using h
  have hprev := st237_p350
  have hstep := st237_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p352 : ((386301317959/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT237 (i+1))
      = (∑ i ∈ Finset.range 351, stT237 (i+1)) + stT237 352 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 351
    simpa using h
  have hprev := st237_p351
  have hstep := st237_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p353 : ((3101222322793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT237 (i+1))
      = (∑ i ∈ Finset.range 352, stT237 (i+1)) + stT237 353 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 352
    simpa using h
  have hprev := st237_p352
  have hstep := st237_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p354 : ((6054788425151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT237 (i+1))
      = (∑ i ∈ Finset.range 353, stT237 (i+1)) + stT237 354 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 353
    simpa using h
  have hprev := st237_p353
  have hstep := st237_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p355 : ((11604626588047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT237 (i+1))
      = (∑ i ∈ Finset.range 354, stT237 (i+1)) + stT237 355 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 354
    simpa using h
  have hprev := st237_p354
  have hstep := st237_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p356 : ((5553683608137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT237 (i+1))
      = (∑ i ∈ Finset.range 355, stT237 (i+1)) + stT237 356 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 355
    simpa using h
  have hprev := st237_p355
  have hstep := st237_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p357 : ((541477957923/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT237 (i+1))
      = (∑ i ∈ Finset.range 356, stT237 (i+1)) + stT237 357 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 356
    simpa using h
  have hprev := st237_p356
  have hstep := st237_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p358 : ((340242495903/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT237 (i+1))
      = (∑ i ∈ Finset.range 357, stT237 (i+1)) + stT237 358 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 357
    simpa using h
  have hprev := st237_p357
  have hstep := st237_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p359 : ((11255700470967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT237 (i+1))
      = (∑ i ∈ Finset.range 358, stT237 (i+1)) + stT237 359 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 358
    simpa using h
  have hprev := st237_p358
  have hstep := st237_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p360 : ((11777559811281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT237 (i+1))
      = (∑ i ∈ Finset.range 359, stT237 (i+1)) + stT237 360 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 359
    simpa using h
  have hprev := st237_p359
  have hstep := st237_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p361 : ((12234967546221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT237 (i+1))
      = (∑ i ∈ Finset.range 360, stT237 (i+1)) + stT237 361 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 360
    simpa using h
  have hprev := st237_p360
  have hstep := st237_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p362 : ((12438558788313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT237 (i+1))
      = (∑ i ∈ Finset.range 361, stT237 (i+1)) + stT237 362 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 361
    simpa using h
  have hprev := st237_p361
  have hstep := st237_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p363 : ((12305645903001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT237 (i+1))
      = (∑ i ∈ Finset.range 362, stT237 (i+1)) + stT237 363 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 362
    simpa using h
  have hprev := st237_p362
  have hstep := st237_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p364 : ((11892465024387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT237 (i+1))
      = (∑ i ∈ Finset.range 363, stT237 (i+1)) + stT237 364 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 363
    simpa using h
  have hprev := st237_p363
  have hstep := st237_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p365 : ((11369056727107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT237 (i+1))
      = (∑ i ∈ Finset.range 364, stT237 (i+1)) + stT237 365 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 364
    simpa using h
  have hprev := st237_p364
  have hstep := st237_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p366 : ((10948461021093/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT237 (i+1))
      = (∑ i ∈ Finset.range 365, stT237 (i+1)) + stT237 366 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 365
    simpa using h
  have hprev := st237_p365
  have hstep := st237_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p367 : ((10799999094741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT237 (i+1))
      = (∑ i ∈ Finset.range 366, stT237 (i+1)) + stT237 367 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 366
    simpa using h
  have hprev := st237_p366
  have hstep := st237_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p368 : ((10981929472599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT237 (i+1))
      = (∑ i ∈ Finset.range 367, stT237 (i+1)) + stT237 368 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 367
    simpa using h
  have hprev := st237_p367
  have hstep := st237_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p369 : ((11419872803297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT237 (i+1))
      = (∑ i ∈ Finset.range 368, stT237 (i+1)) + stT237 369 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 368
    simpa using h
  have hprev := st237_p368
  have hstep := st237_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p370 : ((11938436678547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT237 (i+1))
      = (∑ i ∈ Finset.range 369, stT237 (i+1)) + stT237 370 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 369
    simpa using h
  have hprev := st237_p369
  have hstep := st237_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p371 : ((12332135667879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT237 (i+1))
      = (∑ i ∈ Finset.range 370, stT237 (i+1)) + stT237 371 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 370
    simpa using h
  have hprev := st237_p370
  have hstep := st237_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p372 : ((12446697903879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT237 (i+1))
      = (∑ i ∈ Finset.range 371, stT237 (i+1)) + stT237 372 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 371
    simpa using h
  have hprev := st237_p371
  have hstep := st237_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p373 : ((12238665924823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT237 (i+1))
      = (∑ i ∈ Finset.range 372, stT237 (i+1)) + stT237 373 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 372
    simpa using h
  have hprev := st237_p372
  have hstep := st237_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p374 : ((11790641749367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT237 (i+1))
      = (∑ i ∈ Finset.range 373, stT237 (i+1)) + stT237 374 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 373
    simpa using h
  have hprev := st237_p373
  have hstep := st237_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p375 : ((11277338006183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT237 (i+1))
      = (∑ i ∈ Finset.range 374, stT237 (i+1)) + stT237 375 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 374
    simpa using h
  have hprev := st237_p374
  have hstep := st237_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p376 : ((2724218182911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT237 (i+1))
      = (∑ i ∈ Finset.range 375, stT237 (i+1)) + stT237 376 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 375
    simpa using h
  have hprev := st237_p375
  have hstep := st237_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p377 : ((337326058167/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT237 (i+1))
      = (∑ i ∈ Finset.range 376, stT237 (i+1)) + stT237 377 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 376
    simpa using h
  have hprev := st237_p376
  have hstep := st237_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p378 : ((1375964289513/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT237 (i+1))
      = (∑ i ∈ Finset.range 377, stT237 (i+1)) + stT237 378 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 377
    simpa using h
  have hprev := st237_p377
  have hstep := st237_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p379 : ((11454223267669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT237 (i+1))
      = (∑ i ∈ Finset.range 378, stT237 (i+1)) + stT237 379 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 378
    simpa using h
  have hprev := st237_p378
  have hstep := st237_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p380 : ((5982112566361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT237 (i+1))
      = (∑ i ∈ Finset.range 379, stT237 (i+1)) + stT237 380 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 379
    simpa using h
  have hprev := st237_p379
  have hstep := st237_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p381 : ((12345838842237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT237 (i+1))
      = (∑ i ∈ Finset.range 380, stT237 (i+1)) + stT237 381 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 380
    simpa using h
  have hprev := st237_p380
  have hstep := st237_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p382 : ((2491412207649/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT237 (i+1))
      = (∑ i ∈ Finset.range 381, stT237 (i+1)) + stT237 382 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 381
    simpa using h
  have hprev := st237_p381
  have hstep := st237_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p383 : ((12257860742611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT237 (i+1))
      = (∑ i ∈ Finset.range 382, stT237 (i+1)) + stT237 383 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 382
    simpa using h
  have hprev := st237_p382
  have hstep := st237_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p384 : ((5911710625579/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT237 (i+1))
      = (∑ i ∈ Finset.range 383, stT237 (i+1)) + stT237 384 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 383
    simpa using h
  have hprev := st237_p383
  have hstep := st237_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p385 : ((5657395509107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT237 (i+1))
      = (∑ i ∈ Finset.range 384, stT237 (i+1)) + stT237 385 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 384
    simpa using h
  have hprev := st237_p384
  have hstep := st237_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p386 : ((2729650156821/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT237 (i+1))
      = (∑ i ∈ Finset.range 385, stT237 (i+1)) + stT237 386 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 385
    simpa using h
  have hprev := st237_p385
  have hstep := st237_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p387 : ((10778668328493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT237 (i+1))
      = (∑ i ∈ Finset.range 386, stT237 (i+1)) + stT237 387 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 386
    simpa using h
  have hprev := st237_p386
  have hstep := st237_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p388 : ((547224706477/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT237 (i+1))
      = (∑ i ∈ Finset.range 387, stT237 (i+1)) + stT237 388 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 387
    simpa using h
  have hprev := st237_p387
  have hstep := st237_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p389 : ((113547635591/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT237 (i+1))
      = (∑ i ∈ Finset.range 388, stT237 (i+1)) + stT237 389 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 388
    simpa using h
  have hprev := st237_p388
  have hstep := st237_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p390 : ((593050551527/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT237 (i+1))
      = (∑ i ∈ Finset.range 389, stT237 (i+1)) + stT237 390 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 389
    simpa using h
  have hprev := st237_p389
  have hstep := st237_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p391 : ((6140966872351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT237 (i+1))
      = (∑ i ∈ Finset.range 390, stT237 (i+1)) + stT237 391 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 390
    simpa using h
  have hprev := st237_p390
  have hstep := st237_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p392 : ((6234157434959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT237 (i+1))
      = (∑ i ∈ Finset.range 391, stT237 (i+1)) + stT237 392 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 391
    simpa using h
  have hprev := st237_p391
  have hstep := st237_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p393 : ((6177670915639/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT237 (i+1))
      = (∑ i ∈ Finset.range 392, stT237 (i+1)) + stT237 393 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 392
    simpa using h
  have hprev := st237_p392
  have hstep := st237_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p394 : ((599209725271/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT237 (i+1))
      = (∑ i ∈ Finset.range 393, stT237 (i+1)) + stT237 394 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 393
    simpa using h
  have hprev := st237_p393
  have hstep := st237_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p395 : ((229721481487/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT237 (i+1))
      = (∑ i ∈ Finset.range 394, stT237 (i+1)) + stT237 395 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 394
    simpa using h
  have hprev := st237_p394
  have hstep := st237_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p396 : ((275879220021/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT237 (i+1))
      = (∑ i ∈ Finset.range 395, stT237 (i+1)) + stT237 396 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 395
    simpa using h
  have hprev := st237_p395
  have hstep := st237_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p397 : ((5393807016613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT237 (i+1))
      = (∑ i ∈ Finset.range 396, stT237 (i+1)) + stT237 397 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 396
    simpa using h
  have hprev := st237_p396
  have hstep := st237_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p398 : ((5413943392301/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT237 (i+1))
      = (∑ i ∈ Finset.range 397, stT237 (i+1)) + stT237 398 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 397
    simpa using h
  have hprev := st237_p397
  have hstep := st237_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p399 : ((5570391520431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT237 (i+1))
      = (∑ i ∈ Finset.range 398, stT237 (i+1)) + stT237 399 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 398
    simpa using h
  have hprev := st237_p398
  have hstep := st237_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p400 : ((5809038520431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT237 (i+1))
      = (∑ i ∈ Finset.range 399, stT237 (i+1)) + stT237 400 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 399
    simpa using h
  have hprev := st237_p399
  have hstep := st237_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p401 : ((6048330011487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT237 (i+1))
      = (∑ i ∈ Finset.range 400, stT237 (i+1)) + stT237 401 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 400
    simpa using h
  have hprev := st237_p400
  have hstep := st237_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p402 : ((248290757847/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT237 (i+1))
      = (∑ i ∈ Finset.range 401, stT237 (i+1)) + stT237 402 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 401
    simpa using h
  have hprev := st237_p401
  have hstep := st237_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p403 : ((2493075211209/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT237 (i+1))
      = (∑ i ∈ Finset.range 402, stT237 (i+1)) + stT237 403 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 402
    simpa using h
  have hprev := st237_p402
  have hstep := st237_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p404 : ((12233372000927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT237 (i+1))
      = (∑ i ∈ Finset.range 403, stT237 (i+1)) + stT237 404 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 403
    simpa using h
  have hprev := st237_p403
  have hstep := st237_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p405 : ((11797228428239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT237 (i+1))
      = (∑ i ∈ Finset.range 404, stT237 (i+1)) + stT237 405 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 404
    simpa using h
  have hprev := st237_p404
  have hstep := st237_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p406 : ((11302688835291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT237 (i+1))
      = (∑ i ∈ Finset.range 405, stT237 (i+1)) + stT237 406 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 405
    simpa using h
  have hprev := st237_p405
  have hstep := st237_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p407 : ((10913422325461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT237 (i+1))
      = (∑ i ∈ Finset.range 406, stT237 (i+1)) + stT237 407 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 406
    simpa using h
  have hprev := st237_p406
  have hstep := st237_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p408 : ((430277890269/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT237 (i+1))
      = (∑ i ∈ Finset.range 407, stT237 (i+1)) + stT237 408 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 407
    simpa using h
  have hprev := st237_p407
  have hstep := st237_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p409 : ((10883395580493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT237 (i+1))
      = (∑ i ∈ Finset.range 408, stT237 (i+1)) + stT237 409 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 408
    simpa using h
  have hprev := st237_p408
  have hstep := st237_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p410 : ((2250053280761/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT237 (i+1))
      = (∑ i ∈ Finset.range 409, stT237 (i+1)) + stT237 410 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 409
    simpa using h
  have hprev := st237_p409
  have hstep := st237_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p411 : ((2934378022117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT237 (i+1))
      = (∑ i ∈ Finset.range 410, stT237 (i+1)) + stT237 411 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 410
    simpa using h
  have hprev := st237_p410
  have hstep := st237_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p412 : ((3046838556563/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT237 (i+1))
      = (∑ i ∈ Finset.range 411, stT237 (i+1)) + stT237 412 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 411
    simpa using h
  have hprev := st237_p411
  have hstep := st237_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p413 : ((2491099160899/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT237 (i+1))
      = (∑ i ∈ Finset.range 412, stT237 (i+1)) + stT237 413 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 412
    simpa using h
  have hprev := st237_p412
  have hstep := st237_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p414 : ((778565338679/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT237 (i+1))
      = (∑ i ∈ Finset.range 413, stT237 (i+1)) + stT237 414 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 413
    simpa using h
  have hprev := st237_p413
  have hstep := st237_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p415 : ((2438542280011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT237 (i+1))
      = (∑ i ∈ Finset.range 414, stT237 (i+1)) + stT237 415 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 414
    simpa using h
  have hprev := st237_p414
  have hstep := st237_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p416 : ((734212695527/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT237 (i+1))
      = (∑ i ∈ Finset.range 415, stT237 (i+1)) + stT237 416 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 415
    simpa using h
  have hprev := st237_p415
  have hstep := st237_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p417 : ((11262278361779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT237 (i+1))
      = (∑ i ∈ Finset.range 416, stT237 (i+1)) + stT237 417 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 416
    simpa using h
  have hprev := st237_p416
  have hstep := st237_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p418 : ((10889697672591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT237 (i+1))
      = (∑ i ∈ Finset.range 417, stT237 (i+1)) + stT237 418 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 417
    simpa using h
  have hprev := st237_p417
  have hstep := st237_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p419 : ((2149096800651/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT237 (i+1))
      = (∑ i ∈ Finset.range 418, stT237 (i+1)) + stT237 419 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 418
    simpa using h
  have hprev := st237_p418
  have hstep := st237_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p420 : ((2174684605881/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT237 (i+1))
      = (∑ i ∈ Finset.range 419, stT237 (i+1)) + stT237 420 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 419
    simpa using h
  have hprev := st237_p419
  have hstep := st237_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p421 : ((2246540391727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT237 (i+1))
      = (∑ i ∈ Finset.range 420, stT237 (i+1)) + stT237 421 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 420
    simpa using h
  have hprev := st237_p420
  have hstep := st237_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p422 : ((11711643464051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT237 (i+1))
      = (∑ i ∈ Finset.range 421, stT237 (i+1)) + stT237 422 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 421
    simpa using h
  have hprev := st237_p421
  have hstep := st237_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p423 : ((12162901992299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT237 (i+1))
      = (∑ i ∈ Finset.range 422, stT237 (i+1)) + stT237 423 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 422
    simpa using h
  have hprev := st237_p422
  have hstep := st237_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p424 : ((12448909192791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT237 (i+1))
      = (∑ i ∈ Finset.range 423, stT237 (i+1)) + stT237 424 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 423
    simpa using h
  have hprev := st237_p423
  have hstep := st237_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p425 : ((124835330757/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT237 (i+1))
      = (∑ i ∈ Finset.range 424, stT237 (i+1)) + stT237 425 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 424
    simpa using h
  have hprev := st237_p424
  have hstep := st237_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p426 : ((6128706300393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT237 (i+1))
      = (∑ i ∈ Finset.range 425, stT237 (i+1)) + stT237 426 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 425
    simpa using h
  have hprev := st237_p425
  have hstep := st237_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p427 : ((5919873777439/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT237 (i+1))
      = (∑ i ∈ Finset.range 426, stT237 (i+1)) + stT237 427 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 426
    simpa using h
  have hprev := st237_p426
  have hstep := st237_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p428 : ((11356502780711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT237 (i+1))
      = (∑ i ∈ Finset.range 427, stT237 (i+1)) + stT237 428 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 427
    simpa using h
  have hprev := st237_p427
  have hstep := st237_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p429 : ((2738017758389/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT237 (i+1))
      = (∑ i ∈ Finset.range 428, stT237 (i+1)) + stT237 429 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 428
    simpa using h
  have hprev := st237_p428
  have hstep := st237_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p430 : ((10746157612743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT237 (i+1))
      = (∑ i ∈ Finset.range 429, stT237 (i+1)) + stT237 430 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 429
    simpa using h
  have hprev := st237_p429
  have hstep := st237_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p431 : ((215974463937/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT237 (i+1))
      = (∑ i ∈ Finset.range 430, stT237 (i+1)) + stT237 431 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 430
    simpa using h
  have hprev := st237_p430
  have hstep := st237_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p432 : ((443726771649/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT237 (i+1))
      = (∑ i ∈ Finset.range 431, stT237 (i+1)) + stT237 432 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 431
    simpa using h
  have hprev := st237_p431
  have hstep := st237_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p433 : ((5771099994731/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT237 (i+1))
      = (∑ i ∈ Finset.range 432, stT237 (i+1)) + stT237 433 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 432
    simpa using h
  have hprev := st237_p432
  have hstep := st237_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p434 : ((750888441217/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT237 (i+1))
      = (∑ i ∈ Finset.range 433, stT237 (i+1)) + stT237 434 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 433
    simpa using h
  have hprev := st237_p433
  have hstep := st237_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p435 : ((3093027793687/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT237 (i+1))
      = (∑ i ∈ Finset.range 434, stT237 (i+1)) + stT237 435 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 434
    simpa using h
  have hprev := st237_p434
  have hstep := st237_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p436 : ((12512970503047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT237 (i+1))
      = (∑ i ∈ Finset.range 435, stT237 (i+1)) + stT237 436 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 435
    simpa using h
  have hprev := st237_p435
  have hstep := st237_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p437 : ((12397216697077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT237 (i+1))
      = (∑ i ∈ Finset.range 436, stT237 (i+1)) + stT237 437 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 436
    simpa using h
  have hprev := st237_p436
  have hstep := st237_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p438 : ((12059090948641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT237 (i+1))
      = (∑ i ∈ Finset.range 437, stT237 (i+1)) + stT237 438 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 437
    simpa using h
  have hprev := st237_p437
  have hstep := st237_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p439 : ((2319191333633/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT237 (i+1))
      = (∑ i ∈ Finset.range 438, stT237 (i+1)) + stT237 439 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 438
    simpa using h
  have hprev := st237_p438
  have hstep := st237_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p440 : ((11139796607429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT237 (i+1))
      = (∑ i ∈ Finset.range 439, stT237 (i+1)) + stT237 440 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 439
    simpa using h
  have hprev := st237_p439
  have hstep := st237_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p441 : ((2704867278053/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT237 (i+1))
      = (∑ i ∈ Finset.range 440, stT237 (i+1)) + stT237 441 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 440
    simpa using h
  have hprev := st237_p440
  have hstep := st237_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p442 : ((2681124870647/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT237 (i+1))
      = (∑ i ∈ Finset.range 441, stT237 (i+1)) + stT237 442 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 441
    simpa using h
  have hprev := st237_p441
  have hstep := st237_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p443 : ((1360064320903/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT237 (i+1))
      = (∑ i ∈ Finset.range 442, stT237 (i+1)) + stT237 443 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 442
    simpa using h
  have hprev := st237_p442
  have hstep := st237_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p444 : ((1405365638471/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT237 (i+1))
      = (∑ i ∈ Finset.range 443, stT237 (i+1)) + stT237 444 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 443
    simpa using h
  have hprev := st237_p443
  have hstep := st237_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p445 : ((11710224921463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT237 (i+1))
      = (∑ i ∈ Finset.range 444, stT237 (i+1)) + stT237 445 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 444
    simpa using h
  have hprev := st237_p444
  have hstep := st237_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p446 : ((2430558201167/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT237 (i+1))
      = (∑ i ∈ Finset.range 445, stT237 (i+1)) + stT237 446 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 445
    simpa using h
  have hprev := st237_p445
  have hstep := st237_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p447 : ((12448928500033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT237 (i+1))
      = (∑ i ∈ Finset.range 446, stT237 (i+1)) + stT237 447 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 446
    simpa using h
  have hprev := st237_p446
  have hstep := st237_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p448 : ((12518100636583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT237 (i+1))
      = (∑ i ∈ Finset.range 447, stT237 (i+1)) + stT237 448 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 447
    simpa using h
  have hprev := st237_p447
  have hstep := st237_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p449 : ((12342403457233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT237 (i+1))
      = (∑ i ∈ Finset.range 448, stT237 (i+1)) + stT237 449 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 448
    simpa using h
  have hprev := st237_p448
  have hstep := st237_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p450 : ((5985293031659/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT237 (i+1))
      = (∑ i ∈ Finset.range 449, stT237 (i+1)) + stT237 450 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 449
    simpa using h
  have hprev := st237_p449
  have hstep := st237_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p451 : ((2876007514063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT237 (i+1))
      = (∑ i ∈ Finset.range 450, stT237 (i+1)) + stT237 451 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 450
    simpa using h
  have hprev := st237_p450
  have hstep := st237_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p452 : ((11068765982989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT237 (i+1))
      = (∑ i ∈ Finset.range 451, stT237 (i+1)) + stT237 452 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 451
    simpa using h
  have hprev := st237_p451
  have hstep := st237_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p453 : ((10781365182971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT237 (i+1))
      = (∑ i ∈ Finset.range 452, stT237 (i+1)) + stT237 453 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 452
    simpa using h
  have hprev := st237_p452
  have hstep := st237_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p454 : ((10717916332763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT237 (i+1))
      = (∑ i ∈ Finset.range 453, stT237 (i+1)) + stT237 454 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 453
    simpa using h
  have hprev := st237_p453
  have hstep := st237_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p455 : ((2178870932011/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT237 (i+1))
      = (∑ i ∈ Finset.range 454, stT237 (i+1)) + stT237 455 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 454
    simpa using h
  have hprev := st237_p454
  have hstep := st237_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p456 : ((11262961810307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT237 (i+1))
      = (∑ i ∈ Finset.range 455, stT237 (i+1)) + stT237 456 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 455
    simpa using h
  have hprev := st237_p455
  have hstep := st237_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p457 : ((11725781003407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT237 (i+1))
      = (∑ i ∈ Finset.range 456, stT237 (i+1)) + stT237 457 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 456
    simpa using h
  have hprev := st237_p456
  have hstep := st237_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p458 : ((12160962641177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT237 (i+1))
      = (∑ i ∈ Finset.range 457, stT237 (i+1)) + stT237 458 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 457
    simpa using h
  have hprev := st237_p457
  have hstep := st237_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p459 : ((12454893548937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT237 (i+1))
      = (∑ i ∈ Finset.range 458, stT237 (i+1)) + stT237 459 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 458
    simpa using h
  have hprev := st237_p458
  have hstep := st237_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p460 : ((12531685719589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT237 (i+1))
      = (∑ i ∈ Finset.range 459, stT237 (i+1)) + stT237 460 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 459
    simpa using h
  have hprev := st237_p459
  have hstep := st237_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p461 : ((494892991783/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT237 (i+1))
      = (∑ i ∈ Finset.range 460, stT237 (i+1)) + stT237 461 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 460
    simpa using h
  have hprev := st237_p460
  have hstep := st237_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p462 : ((12018903880111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT237 (i+1))
      = (∑ i ∈ Finset.range 461, stT237 (i+1)) + stT237 462 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 461
    simpa using h
  have hprev := st237_p461
  have hstep := st237_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p463 : ((11563007882311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT237 (i+1))
      = (∑ i ∈ Finset.range 462, stT237 (i+1)) + stT237 463 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 462
    simpa using h
  have hprev := st237_p462
  have hstep := st237_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p464 : ((1112168418359/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT237 (i+1))
      = (∑ i ∈ Finset.range 463, stT237 (i+1)) + stT237 464 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 463
    simpa using h
  have hprev := st237_p463
  have hstep := st237_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p465 : ((2701824009613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT237 (i+1))
      = (∑ i ∈ Finset.range 464, stT237 (i+1)) + stT237 465 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 464
    simpa using h
  have hprev := st237_p464
  have hstep := st237_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p466 : ((2674766044393/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT237 (i+1))
      = (∑ i ∈ Finset.range 465, stT237 (i+1)) + stT237 466 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 465
    simpa using h
  have hprev := st237_p465
  have hstep := st237_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p467 : ((2705869845097/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT237 (i+1))
      = (∑ i ∈ Finset.range 466, stT237 (i+1)) + stT237 467 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 466
    simpa using h
  have hprev := st237_p466
  have hstep := st237_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p468 : ((1393535842361/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT237 (i+1))
      = (∑ i ∈ Finset.range 467, stT237 (i+1)) + stT237 468 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 467
    simpa using h
  have hprev := st237_p467
  have hstep := st237_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p469 : ((2318260296803/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT237 (i+1))
      = (∑ i ∈ Finset.range 468, stT237 (i+1)) + stT237 469 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 468
    simpa using h
  have hprev := st237_p468
  have hstep := st237_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p470 : ((6020759363/5000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT237 (i+1))
      = (∑ i ∈ Finset.range 469, stT237 (i+1)) + stT237 470 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 469
    simpa using h
  have hprev := st237_p469
  have hstep := st237_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p471 : ((1981929361/1600000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT237 (i+1))
      = (∑ i ∈ Finset.range 470, stT237 (i+1)) + stT237 471 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 470
    simpa using h
  have hprev := st237_p470
  have hstep := st237_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p472 : ((391964177759/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT237 (i+1))
      = (∑ i ∈ Finset.range 471, stT237 (i+1)) + stT237 472 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 471
    simpa using h
  have hprev := st237_p471
  have hstep := st237_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p473 : ((6235641911717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT237 (i+1))
      = (∑ i ∈ Finset.range 472, stT237 (i+1)) + stT237 473 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 472
    simpa using h
  have hprev := st237_p472
  have hstep := st237_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p474 : ((6095407684441/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT237 (i+1))
      = (∑ i ∈ Finset.range 473, stT237 (i+1)) + stT237 474 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 473
    simpa using h
  have hprev := st237_p473
  have hstep := st237_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p475 : ((5885411060593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT237 (i+1))
      = (∑ i ∈ Finset.range 474, stT237 (i+1)) + stT237 475 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 474
    simpa using h
  have hprev := st237_p474
  have hstep := st237_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p476 : ((176782192249/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT237 (i+1))
      = (∑ i ∈ Finset.range 475, stT237 (i+1)) + stT237 476 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 475
    simpa using h
  have hprev := st237_p475
  have hstep := st237_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p477 : ((10931359199797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT237 (i+1))
      = (∑ i ∈ Finset.range 476, stT237 (i+1)) + stT237 477 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 476
    simpa using h
  have hprev := st237_p476
  have hstep := st237_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p478 : ((10714784577407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT237 (i+1))
      = (∑ i ∈ Finset.range 477, stT237 (i+1)) + stT237 478 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 477
    simpa using h
  have hprev := st237_p477
  have hstep := st237_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p479 : ((2143142238583/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT237 (i+1))
      = (∑ i ∈ Finset.range 478, stT237 (i+1)) + stT237 479 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 478
    simpa using h
  have hprev := st237_p478
  have hstep := st237_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p480 : ((2186611464817/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT237 (i+1))
      = (∑ i ∈ Finset.range 479, stT237 (i+1)) + stT237 480 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 479
    simpa using h
  have hprev := st237_p479
  have hstep := st237_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p481 : ((18102600701/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT237 (i+1))
      = (∑ i ∈ Finset.range 480, stT237 (i+1)) + stT237 481 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 480
    simpa using h
  have hprev := st237_p480
  have hstep := st237_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p482 : ((2941946825429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT237 (i+1))
      = (∑ i ∈ Finset.range 481, stT237 (i+1)) + stT237 482 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 481
    simpa using h
  have hprev := st237_p481
  have hstep := st237_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p483 : ((12186470719011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT237 (i+1))
      = (∑ i ∈ Finset.range 482, stT237 (i+1)) + stT237 483 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 482
    simpa using h
  have hprev := st237_p482
  have hstep := st237_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p484 : ((6235850444163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT237 (i+1))
      = (∑ i ∈ Finset.range 483, stT237 (i+1)) + stT237 484 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 483
    simpa using h
  have hprev := st237_p483
  have hstep := st237_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p485 : ((6278554021583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT237 (i+1))
      = (∑ i ∈ Finset.range 484, stT237 (i+1)) + stT237 485 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 484
    simpa using h
  have hprev := st237_p484
  have hstep := st237_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p486 : ((6211754505763/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT237 (i+1))
      = (∑ i ∈ Finset.range 485, stT237 (i+1)) + stT237 486 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 485
    simpa using h
  have hprev := st237_p485
  have hstep := st237_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p487 : ((1210285344167/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT237 (i+1))
      = (∑ i ∈ Finset.range 486, stT237 (i+1)) + stT237 487 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 486
    simpa using h
  have hprev := st237_p486
  have hstep := st237_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p488 : ((466807223603/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT237 (i+1))
      = (∑ i ∈ Finset.range 487, stT237 (i+1)) + stT237 488 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 487
    simpa using h
  have hprev := st237_p487
  have hstep := st237_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p489 : ((11225788831307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT237 (i+1))
      = (∑ i ∈ Finset.range 488, stT237 (i+1)) + stT237 489 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 488
    simpa using h
  have hprev := st237_p488
  have hstep := st237_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p490 : ((10871875712627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT237 (i+1))
      = (∑ i ∈ Finset.range 489, stT237 (i+1)) + stT237 490 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 489
    simpa using h
  have hprev := st237_p489
  have hstep := st237_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p491 : ((10689122402151/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT237 (i+1))
      = (∑ i ∈ Finset.range 490, stT237 (i+1)) + stT237 491 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 490
    simpa using h
  have hprev := st237_p490
  have hstep := st237_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p492 : ((10718530303971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT237 (i+1))
      = (∑ i ∈ Finset.range 491, stT237 (i+1)) + stT237 492 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 491
    simpa using h
  have hprev := st237_p491
  have hstep := st237_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p493 : ((54762904361/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT237 (i+1))
      = (∑ i ∈ Finset.range 492, stT237 (i+1)) + stT237 493 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 492
    simpa using h
  have hprev := st237_p492
  have hstep := st237_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p494 : ((11337529230511/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT237 (i+1))
      = (∑ i ∈ Finset.range 493, stT237 (i+1)) + stT237 494 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 493
    simpa using h
  have hprev := st237_p493
  have hstep := st237_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p495 : ((11786031125941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT237 (i+1))
      = (∑ i ∈ Finset.range 494, stT237 (i+1)) + stT237 495 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 494
    simpa using h
  have hprev := st237_p494
  have hstep := st237_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p496 : ((121971667363/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT237 (i+1))
      = (∑ i ∈ Finset.range 495, stT237 (i+1)) + stT237 496 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 495
    simpa using h
  have hprev := st237_p495
  have hstep := st237_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p497 : ((3119789325079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT237 (i+1))
      = (∑ i ∈ Finset.range 496, stT237 (i+1)) + stT237 497 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 496
    simpa using h
  have hprev := st237_p496
  have hstep := st237_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p498 : ((1571213136947/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT237 (i+1))
      = (∑ i ∈ Finset.range 497, stT237 (i+1)) + stT237 498 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 497
    simpa using h
  have hprev := st237_p497
  have hstep := st237_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p499 : ((1556181989973/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT237 (i+1))
      = (∑ i ∈ Finset.range 498, stT237 (i+1)) + stT237 499 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 498
    simpa using h
  have hprev := st237_p498
  have hstep := st237_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_p500 : ((3036445602127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT237 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT237 (i+1))
      = (∑ i ∈ Finset.range 499, stT237 (i+1)) + stT237 500 := by
    have h := Finset.sum_range_succ (fun i => stT237 (i+1)) 499
    simpa using h
  have hprev := st237_p499
  have hstep := st237_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st237_s500 :
    |Real.sin (((237 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((69893/250000 : ℚ) : ℝ))
      - ((734153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1158587/2000000) (δ := 5941/500000000) (ψ := 69893/250000) 237 234
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 237`** (evaluated boundary). -/
theorem station_237_sign : hardyG ((((237:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 237 500 (by norm_num) (by norm_num)
    ((69893/250000 : ℚ) : ℝ)
  have hchain := st237_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT237 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((237 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((69893/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st237_c500
  have hsinb := abs_le.mp st237_s500
  have hbdy_lo : ((-9708269316227/140423125000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((237 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((69893/250000 : ℚ) : ℝ))) / 2
          - ((((237:ℕ)):ℝ))
            * Real.sin (((237 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((69893/250000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((237:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((237:ℝ) * Real.log (500:ℝ) - ((69893/250000 : ℚ) : ℝ))) / 2
        - ((237:ℝ)) * Real.sin ((237:ℝ) * Real.log (500:ℝ) - ((69893/250000 : ℚ) : ℝ))
        ≥ ((-43416661/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((237:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-43416661/250000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-43416661/250000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-43416661/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((237:ℕ)):ℝ))+1) * (((((237:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((6714096007061/15000000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((3036445602127/2500000000000 : ℚ) : ℝ) + ((-9708269316227/140423125000000 : ℚ) : ℝ)
      - ((6714096007061/15000000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((69893/250000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((237:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((69893/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((237:ℕ)):ℝ)))).re
      - Real.sin ((69893/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((237:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((237:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((237:ℕ)):ℝ))
      = (((((237:ℕ)):ℝ)) * (Real.log ((((237:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((237:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_237
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
  have hθwin : |(((69893/250000 : ℚ) : ℝ) + ((50:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((237:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((237:ℕ)):ℝ)))
    (φ := ((69893/250000 : ℚ) : ℝ) + ((50:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((69893/250000 : ℚ) : ℝ) + ((50:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((69893/250000 : ℚ)) : ℝ) - Real.pi) + ((50:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((69893/250000 : ℚ)) : ℝ) - Real.pi) 50).1,
    (cos_sin_shift ((((69893/250000 : ℚ)) : ℝ) - Real.pi) 50).2]
  exact cos_sin_flip ((69893/250000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_237_sign
end AxiomAudit
