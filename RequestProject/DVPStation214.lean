import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 214` (rung-217.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT214 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((214 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-4983/100000 : ℚ) : ℝ))

theorem st214_c1 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((998759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4983/400000) (δ := 1/1000000000) (ψ := -4983/100000) 214 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t1 : ((998709/1000000 : ℚ) : ℝ) ≤ stT214 1 := by
  have hc : ((998709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((998709/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((998709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c2 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-746197/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3016409/5000000) (δ := 5387/500000000) (ψ := -4983/100000) 214 24
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t2 : ((-1319190820449/2500000000000 : ℚ) : ℝ) ≤ stT214 2 := by
  have hc : ((-746247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1319190820449/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-746247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c3 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-55819/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52246/78125) (δ := 10767/1000000000) (ψ := -4983/100000) 214 37
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t3 : ((-2578313649231/5000000000000 : ℚ) : ℝ) ≤ stT214 3 := by
  have hc : ((-446577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2578313649231/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-446577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c4 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((32591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3517779/10000000) (δ := 10839/1000000000) (ψ := -4983/100000) 214 47
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t4 : ((32581/400000 : ℚ) : ℝ) ≤ stT214 4 := by
  have hc : ((32581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32581/400000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((32581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c5 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((224281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2764101/10000000) (δ := 681/62500000) (ψ := -4983/100000) 214 55
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t5 : ((195879513/976562500 : ℚ) : ℝ) ≤ stT214 5 := by
  have hc : ((7008/15625 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195879513/976562500 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((7008/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c6 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((488801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 530121/10000000) (δ := 679/62500000) (ψ := -4983/100000) 214 61
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t6 : ((124713701377/312500000000 : ℚ) : ℝ) ≤ stT214 6 := by
  have hc : ((61097/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124713701377/312500000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((61097/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c7 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-52989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 446093/1000000) (δ := 87/8000000) (ψ := -4983/100000) 214 66
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t7 : ((-80130741787/1000000000000 : ℚ) : ℝ) ≤ stT214 7 := by
  have hc : ((-106003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-80130741787/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-106003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c8 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((492501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -659897/2500000) (δ := 1349/125000000) (ψ := -4983/100000) 214 71
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t8 : ((1741076761383/10000000000000 : ℚ) : ℝ) ≤ stT214 8 := by
  have hc : ((492451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1741076761383/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((492451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c9 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((554517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38399/156250) (δ := 10763/1000000000) (ψ := -4983/100000) 214 75
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t9 : ((1848223148511/10000000000000 : ℚ) : ℝ) ≤ stT214 9 := by
  have hc : ((554467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1848223148511/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((554467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c10 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-455103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3393221/5000000) (δ := 5381/500000000) (ψ := -4983/100000) 214 78
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t10 : ((-89952578849/312500000000 : ℚ) : ℝ) ≤ stT214 10 := by
  have hc : ((-56891/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89952578849/312500000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-56891/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c11 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-435853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2527227/5000000) (δ := 1079/100000000) (ψ := -4983/100000) 214 82
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t11 : ((-657148618971/5000000000000 : ℚ) : ℝ) ≤ stT214 11 := by
  have hc : ((-435903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-657148618971/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-435903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c12 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-78609/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1125449/2000000) (δ := 1339/125000000) (ψ := -4983/100000) 214 85
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t12 : ((-28367841271/156250000000 : ℚ) : ℝ) ≤ stT214 12 := by
  have hc : ((-314461/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28367841271/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-314461/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c13 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-16877/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5779673/10000000) (δ := 5363/500000000) (ψ := -4983/100000) 214 87
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t13 : ((-187247373013/1000000000000 : ℚ) : ℝ) ≤ stT214 13 := by
  have hc : ((-67513/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187247373013/1000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-67513/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c14 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((194617/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1696437/10000000) (δ := 2151/200000000) (ψ := -4983/100000) 214 90
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t14 : ((260051160977/1250000000000 : ℚ) : ℝ) ≤ stT214 14 := by
  have hc : ((389209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260051160977/1250000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((389209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c15 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((51239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1899419/5000000) (δ := 10741/1000000000) (ψ := -4983/100000) 214 92
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t15 : ((33042345933/2500000000000 : ℚ) : ℝ) ≤ stT214 15 := by
  have hc : ((51189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33042345933/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((51189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c16 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-116213/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6911009/10000000) (δ := 10727/1000000000) (ψ := -4983/100000) 214 94
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t16 : ((-1162192964877/5000000000000 : ℚ) : ℝ) ≤ stT214 16 := by
  have hc : ((-464877/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1162192964877/5000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-464877/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c17 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-999547/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48617/62500) (δ := 2161/200000000) (ψ := -4983/100000) 214 97
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t17 : ((-2424379581129/10000000000000 : ℚ) : ℝ) ≤ stT214 17 := by
  have hc : ((-999597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2424379581129/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-999597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c18 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-238509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7093061/10000000) (δ := 2141/200000000) (ψ := -4983/100000) 214 98
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t18 : ((-1124401322989/5000000000000 : ℚ) : ℝ) ≤ stT214 18 := by
  have hc : ((-477043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1124401322989/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-477043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c19 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-133577/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2301543/5000000) (δ := 2721/250000000) (ψ := -4983/100000) 214 100
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t19 : ((-76626024279/1250000000000 : ℚ) : ℝ) ≤ stT214 19 := by
  have hc : ((-66801/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76626024279/1250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-66801/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c20 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((242127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25163/400000) (δ := 10869/1000000000) (ψ := -4983/100000) 214 102
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t20 : ((1082768487343/5000000000000 : ℚ) : ℝ) ≤ stT214 20 := by
  have hc : ((484229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1082768487343/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((484229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c21 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-298233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2342047/5000000) (δ := 2687/250000000) (ψ := -4983/100000) 214 104
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t21 : ((-650906898657/10000000000000 : ℚ) : ℝ) ≤ stT214 21 := by
  have hc : ((-298283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-650906898657/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-298283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c22 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-225699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4496143/10000000) (δ := 2171/200000000) (ψ := -4983/100000) 214 105
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t22 : ((-60162334249/1250000000000 : ℚ) : ℝ) ≤ stT214 22 := by
  have hc : ((-225749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60162334249/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-225749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c23 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((77589/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3138071/10000000) (δ := 10733/1000000000) (ψ := -4983/100000) 214 107
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t23 : ((40439543379/625000000000 : ℚ) : ℝ) ≤ stT214 23 := by
  have hc : ((155153/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40439543379/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((155153/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c24 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((91/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 490419/1250000) (δ := 10777/1000000000) (ψ := -4983/100000) 214 108
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t24 : ((1434992423/5000000000000 : ℚ) : ℝ) ≤ stT214 24 := by
  have hc : ((703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1434992423/5000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c25 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-159197/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1130561/2000000) (δ := 2703/250000000) (ψ := -4983/100000) 214 110
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t25 : ((-636838318419/5000000000000 : ℚ) : ℝ) ≤ stT214 25 := by
  have hc : ((-318419/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-636838318419/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-318419/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c26 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((98861/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -377693/10000000) (δ := 5449/500000000) (ψ := -4983/100000) 214 111
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t26 : ((24234066477/125000000000 : ℚ) : ℝ) ≤ stT214 26 := by
  have hc : ((12357/12500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24234066477/125000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((12357/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c27 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-14261/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1026351/2500000) (δ := 5403/500000000) (ψ := -4983/100000) 214 112
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t27 : ((-27464553771/2000000000000 : ℚ) : ℝ) ≤ stT214 27 := by
  have hc : ((-14271/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27464553771/2000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-14271/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c28 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7853803/10000000) (δ := 541/50000000) (ψ := -4983/100000) 214 114
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t28 : ((-37798349823/200000000000 : ℚ) : ℝ) ≤ stT214 28 := by
  have hc : ((-20001/20000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37798349823/200000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-20001/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c29 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-168803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4787921/10000000) (δ := 10727/1000000000) (ψ := -4983/100000) 214 115
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t29 : ((-39188228739/625000000000 : ℚ) : ℝ) ≤ stT214 29 := by
  have hc : ((-42207/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39188228739/625000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-42207/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c30 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((146753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1179291/5000000) (δ := 10769/1000000000) (ψ := -4983/100000) 214 116
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t30 : ((535820294421/5000000000000 : ℚ) : ℝ) ≤ stT214 30 := by
  have hc : ((293481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((535820294421/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((293481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c31 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((489059/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -523949/10000000) (δ := 10861/1000000000) (ψ := -4983/100000) 214 117
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t31 : ((439165491401/2500000000000 : ℚ) : ℝ) ≤ stT214 31 := by
  have hc : ((244517/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439165491401/2500000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((244517/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c32 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((190981/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 753643/10000000) (δ := 10849/1000000000) (ψ := -4983/100000) 214 118
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t32 : ((168796020393/1000000000000 : ℚ) : ℝ) ≤ stT214 32 := by
  have hc : ((190971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((168796020393/1000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((190971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c33 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((411707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 301697/2000000) (δ := 10847/1000000000) (ψ := -4983/100000) 214 119
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t33 : ((44790384077/312500000000 : ℚ) : ℝ) ≤ stT214 33 := by
  have hc : ((205841/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44790384077/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((205841/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c34 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((94897/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1771877/10000000) (δ := 537/50000000) (ψ := -4983/100000) 214 120
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t34 : ((130188970311/1000000000000 : ℚ) : ℝ) ≤ stT214 34 := by
  have hc : ((379563/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130188970311/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((379563/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c35 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((808681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 786113/5000000) (δ := 10833/1000000000) (ψ := -4983/100000) 214 121
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t35 : ((341708862087/2500000000000 : ℚ) : ℝ) ≤ stT214 35 := by
  have hc : ((808631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341708862087/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((808631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c36 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((232693/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187139/2000000) (δ := 10877/1000000000) (ψ := -4983/100000) 214 122
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t36 : ((387800678213/2500000000000 : ℚ) : ℝ) ≤ stT214 36 := by
  have hc : ((465361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387800678213/2500000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((465361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c37 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((249741/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28451/2500000) (δ := 5409/500000000) (ψ := -4983/100000) 214 123
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t37 : ((821101813973/5000000000000 : ℚ) : ℝ) ≤ stT214 37 := by
  have hc : ((499457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((821101813973/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((499457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c38 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((812883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -38857/250000) (δ := 10711/1000000000) (ψ := -4983/100000) 214 124
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t38 : ((659294536131/5000000000000 : ℚ) : ℝ) ≤ stT214 38 := by
  have hc : ((812833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((659294536131/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((812833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c39 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((222771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3365351/10000000) (δ := 2701/250000000) (ψ := -4983/100000) 214 125
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t39 : ((356638905601/10000000000000 : ℚ) : ℝ) ≤ stT214 39 := by
  have hc : ((222721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356638905601/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((222721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c40 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-597613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5528291/10000000) (δ := 5353/500000000) (ψ := -4983/100000) 214 126
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t40 : ((-944988278157/10000000000000 : ℚ) : ℝ) ≤ stT214 40 := by
  have hc : ((-597663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-944988278157/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-597663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c41 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-498821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30729/40000) (δ := 5353/500000000) (ψ := -4983/100000) 214 126
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t41 : ((-194766688587/1250000000000 : ℚ) : ℝ) ≤ stT214 41 := by
  have hc : ((-249423/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194766688587/1250000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-249423/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c42 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-367021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4866503/10000000) (δ := 10813/1000000000) (ψ := -4983/100000) 214 127
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t42 : ((-283201516707/5000000000000 : ℚ) : ℝ) ≤ stT214 42 := by
  have hc : ((-367071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283201516707/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-367071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c43 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((765523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1747357/10000000) (δ := 67/6250000) (ψ := -4983/100000) 214 128
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t43 : ((233466968581/2000000000000 : ℚ) : ℝ) ≤ stT214 43 := by
  have hc : ((765473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233466968581/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((765473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c44 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((24601/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207653/1250000) (δ := 431/40000000) (ψ := -4983/100000) 214 129
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t44 : ((148340118399/1250000000000 : ℚ) : ℝ) ≤ stT214 44 := by
  have hc : ((393591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148340118399/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((393591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c45 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-268847/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5346239/10000000) (δ := 2147/200000000) (ψ := -4983/100000) 214 130
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t45 : ((-6262667451/78125000000 : ℚ) : ℝ) ≤ stT214 45 := by
  have hc : ((-33609/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6262667451/78125000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-33609/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c46 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-838319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 801559/1250000) (δ := 2717/250000000) (ψ := -4983/100000) 214 130
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t46 : ((-61805401049/500000000000 : ℚ) : ℝ) ≤ stT214 46 := by
  have hc : ((-838369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61805401049/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-838369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c47 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((316973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110519/500000) (δ := 5421/500000000) (ψ := -4983/100000) 214 131
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t47 : ((115578970813/1250000000000 : ℚ) : ℝ) ≤ stT214 47 := by
  have hc : ((79237/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115578970813/1250000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((79237/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c48 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((313303/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -446803/2000000) (δ := 5427/500000000) (ψ := -4983/100000) 214 132
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t48 : ((1808710533/20000000000 : ℚ) : ℝ) ≤ stT214 48 := by
  have hc : ((156639/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1808710533/20000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((156639/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c49 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-929659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3455353/5000000) (δ := 10747/1000000000) (ψ := -4983/100000) 214 133
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t49 : ((-332039061387/2500000000000 : ℚ) : ℝ) ≤ stT214 49 := by
  have hc : ((-929709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332039061387/2500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-929709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c50 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((11679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60903/156250) (δ := 10747/1000000000) (ψ := -4983/100000) 214 133
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t50 : ((16445882977/10000000000000 : ℚ) : ℝ) ≤ stT214 50 := by
  have hc : ((11629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16445882977/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((11629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c51 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((884063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60789/500000) (δ := 2691/250000000) (ψ := -4983/100000) 214 134
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t51 : ((30946643091/250000000000 : ℚ) : ℝ) ≤ stT214 51 := by
  have hc : ((884013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30946643091/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((884013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c52 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-432017/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -326753/500000) (δ := 2683/250000000) (ψ := -4983/100000) 214 135
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t52 : ((-299567337771/2500000000000 : ℚ) : ℝ) ≤ stT214 52 := by
  have hc : ((-216021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-299567337771/2500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-216021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c53 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((108293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3655727/10000000) (δ := 2683/250000000) (ψ := -4983/100000) 214 135
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t53 : ((29736625203/2000000000000 : ℚ) : ℝ) ≤ stT214 53 := by
  have hc : ((108243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29736625203/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((108243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c54 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((681647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2051963/10000000) (δ := 433/40000000) (ψ := -4983/100000) 214 136
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t54 : ((927535600719/10000000000000 : ℚ) : ℝ) ≤ stT214 54 := by
  have hc : ((681597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((927535600719/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((681597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c55 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-249841/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3882403/5000000) (δ := 5389/500000000) (ψ := -4983/100000) 214 136
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t55 : ((-1684512297/12500000000 : ℚ) : ℝ) ≤ stT214 55 := by
  have hc : ((-499707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1684512297/12500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-499707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c56 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((97299/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 84837/500000) (δ := 5359/500000000) (ψ := -4983/100000) 214 137
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t56 : ((260025771163/2500000000000 : ℚ) : ℝ) ≤ stT214 56 := by
  have hc : ((389171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260025771163/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((389171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c57 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-48701/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4541937/10000000) (δ := 1349/125000000) (ψ := -4983/100000) 214 138
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t57 : ((-64519326963/2000000000000 : ℚ) : ℝ) ≤ stT214 57 := by
  have hc : ((-48711/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64519326963/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-48711/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c58 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-82021/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1190669/2500000) (δ := 1349/125000000) (ψ := -4983/100000) 214 138
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t58 : ((-43086127071/1000000000000 : ℚ) : ℝ) ≤ stT214 58 := by
  have hc : ((-164067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43086127071/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-164067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c59 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((751863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1799783/10000000) (δ := 10899/1000000000) (ψ := -4983/100000) 214 139
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t59 : ((978777074757/10000000000000 : ℚ) : ℝ) ≤ stT214 59 := by
  have hc : ((751813/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((978777074757/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((751813/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c60 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-241287/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1438403/2000000) (δ := 669/62500000) (ψ := -4983/100000) 214 139
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t60 : ((-124606579201/1000000000000 : ℚ) : ℝ) ≤ stT214 60 := by
  have hc : ((-482599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124606579201/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-482599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c61 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((495723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 327227/10000000) (δ := 2699/250000000) (ψ := -4983/100000) 214 140
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t61 : ((19833620527/156250000000 : ℚ) : ℝ) ≤ stT214 61 := by
  have hc : ((247849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19833620527/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((247849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c62 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-223/250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6681369/10000000) (δ := 10889/1000000000) (ψ := -4983/100000) 214 141
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t62 : ((-11329052841/100000000000 : ℚ) : ℝ) ≤ stT214 62 := by
  have hc : ((-17841/20000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11329052841/100000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-17841/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c63 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((9133/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375769/2000000) (δ := 10889/1000000000) (ψ := -4983/100000) 214 141
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t63 : ((92045645979/1000000000000 : ℚ) : ℝ) ≤ stT214 63 := by
  have hc : ((73059/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((92045645979/1000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((73059/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c64 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-111391/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5403777/10000000) (δ := 10821/1000000000) (ψ := -4983/100000) 214 142
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t64 : ((-139251361401/2000000000000 : ℚ) : ℝ) ≤ stT214 64 := by
  have hc : ((-111401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-139251361401/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-111401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c65 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((50331/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289097/1000000) (δ := 10821/1000000000) (ψ := -4983/100000) 214 142
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t65 : ((249680610753/5000000000000 : ℚ) : ℝ) ≤ stT214 65 := by
  have hc : ((201299/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249680610753/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((201299/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c66 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-7119/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4648881/10000000) (δ := 1341/125000000) (ψ := -4983/100000) 214 143
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t66 : ((-7011538023/200000000000 : ℚ) : ℝ) ≤ stT214 66 := by
  have hc : ((-28481/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7011538023/200000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-28481/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c67 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((210649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 679279/2000000) (δ := 87/8000000) (ψ := -4983/100000) 214 143
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t67 : ((128643767353/5000000000000 : ℚ) : ℝ) ≤ stT214 67 := by
  have hc : ((210599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128643767353/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((210599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c68 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-182373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4385489/10000000) (δ := 2167/200000000) (ψ := -4983/100000) 214 144
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t68 : ((-221220541217/10000000000000 : ℚ) : ℝ) ≤ stT214 68 := by
  have hc : ((-182423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221220541217/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-182423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c69 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((199501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3424869/10000000) (δ := 2167/200000000) (ψ := -4983/100000) 214 144
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t69 : ((120055340979/5000000000000 : ℚ) : ℝ) ≤ stT214 69 := by
  have hc : ((199451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120055340979/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((199451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c70 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-260229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -229257/500000) (δ := 10743/1000000000) (ψ := -4983/100000) 214 145
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t70 : ((-311093008891/10000000000000 : ℚ) : ℝ) ≤ stT214 70 := by
  have hc : ((-260279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311093008891/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-260279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c71 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((361007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3003621/10000000) (δ := 10743/1000000000) (ψ := -4983/100000) 214 145
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t71 : ((428376909417/10000000000000 : ℚ) : ℝ) ≤ stT214 71 := by
  have hc : ((360957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428376909417/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((360957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c72 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-495033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -652709/1250000) (δ := 10753/1000000000) (ψ := -4983/100000) 214 146
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t72 : ((-36466328531/625000000000 : ℚ) : ℝ) ≤ stT214 72 := by
  have hc : ((-495083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36466328531/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-495083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c73 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((650087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134859/625000) (δ := 217/20000000) (ψ := -4983/100000) 214 146
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t73 : ((760810455207/10000000000000 : ℚ) : ℝ) ≤ stT214 73 := by
  have hc : ((650037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760810455207/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((650037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c74 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-161239/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -783903/1250000) (δ := 5423/500000000) (ψ := -4983/100000) 214 147
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t74 : ((-187448253773/2000000000000 : ℚ) : ℝ) ≤ stT214 74 := by
  have hc : ((-161249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187448253773/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-161249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c75 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((934461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182027/2000000) (δ := 10757/1000000000) (ψ := -4983/100000) 214 147
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t75 : ((10789643817/100000000000 : ℚ) : ℝ) ≤ stT214 75 := by
  have hc : ((934411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10789643817/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((934411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c76 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-49919/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3855823/5000000) (δ := 679/62500000) (ψ := -4983/100000) 214 148
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t76 : ((-114527808597/1000000000000 : ℚ) : ℝ) ≤ stT214 76 := by
  have hc : ((-99843/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114527808597/1000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-99843/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c77 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((959033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -718073/10000000) (δ := 10739/1000000000) (ψ := -4983/100000) 214 148
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t77 : ((218572364343/2000000000000 : ℚ) : ℝ) ≤ stT214 77 := by
  have hc : ((958983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((218572364343/2000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((958983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c78 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-6283/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3092623/5000000) (δ := 10739/1000000000) (ψ := -4983/100000) 214 148
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t78 : ((-17786388963/200000000000 : ℚ) : ℝ) ≤ stT214 78 := by
  have hc : ((-31417/40000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17786388963/200000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-31417/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c79 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((468733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -338419/1250000) (δ := 10771/1000000000) (ψ := -4983/100000) 214 149
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t79 : ((527309150421/10000000000000 : ℚ) : ℝ) ≤ stT214 79 := by
  have hc : ((468683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((527309150421/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((468683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c80 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-38117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2011153/5000000) (δ := 10771/1000000000) (ψ := -4983/100000) 214 149
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t80 : ((-21336001839/5000000000000 : ℚ) : ℝ) ≤ stT214 80 := by
  have hc : ((-38167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21336001839/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-38167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c81 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-86101/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -251981/500000) (δ := 429/40000000) (ψ := -4983/100000) 214 150
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t81 : ((-11959870679/250000000000 : ℚ) : ℝ) ≤ stT214 81 := by
  have hc : ((-86111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11959870679/250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-86111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c82 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((32787/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381221/2500000) (δ := 5439/500000000) (ψ := -4983/100000) 214 150
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t82 : ((1448198691/16000000000 : ℚ) : ℝ) ≤ stT214 82 := by
  have hc : ((6557/8000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1448198691/16000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((6557/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c83 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-998057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7698131/10000000) (δ := 10817/1000000000) (ψ := -4983/100000) 214 151
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t83 : ((-1095565161801/10000000000000 : ℚ) : ℝ) ≤ stT214 83 := by
  have hc : ((-998107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1095565161801/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-998107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c84 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((108703/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -129089/1000000) (δ := 10793/500000000) (ψ := -4983/100000) 214 151
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t84 : ((474391313043/5000000000000 : ℚ) : ℝ) ≤ stT214 84 := by
  have hc : ((434787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((474391313043/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((434787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c85 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-430837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 252027/500000) (δ := 10817/1000000000) (ψ := -4983/100000) 214 151
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t85 : ((-467362877211/10000000000000 : ℚ) : ℝ) ≤ stT214 85 := by
  have hc : ((-430887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-467362877211/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-430887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c86 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-192029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4410063/10000000) (δ := 1071/100000000) (ψ := -4983/100000) 214 152
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t86 : ((-25890520489/1250000000000 : ℚ) : ℝ) ≤ stT214 86 := by
  have hc : ((-192079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25890520489/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-192079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c87 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((758357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1775019/10000000) (δ := 10893/1000000000) (ψ := -4983/100000) 214 152
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t87 : ((50811877149/625000000000 : ℚ) : ℝ) ≤ stT214 87 := by
  have hc : ((758307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50811877149/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((758307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c88 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-9999/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781859/1000000) (δ := 27/2500000) (ψ := -4983/100000) 214 153
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t88 : ((-5329753499/50000000000 : ℚ) : ℝ) ≤ stT214 88 := by
  have hc : ((-19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5329753499/50000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c89 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((75879/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -886679/5000000) (δ := 10803/1000000000) (ψ := -4983/100000) 214 153
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t89 : ((40213106189/500000000000 : ℚ) : ℝ) ≤ stT214 89 := by
  have hc : ((37937/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40213106189/500000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((37937/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c90 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-110719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2102179/5000000) (δ := 27/2500000) (ψ := -4983/100000) 214 153
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t90 : ((-116760827517/10000000000000 : ℚ) : ℝ) ≤ stT214 90 := by
  have hc : ((-110769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-116760827517/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-110769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c91 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-154457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43687/78125) (δ := 2687/125000000) (ψ := -4983/100000) 214 154
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t91 : ((-64771223923/1000000000000 : ℚ) : ℝ) ≤ stT214 91 := by
  have hc : ((-308939/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64771223923/1000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-308939/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c92 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((497399/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 127553/5000000) (δ := 10707/1000000000) (ψ := -4983/100000) 214 154
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t92 : ((64818525741/625000000000 : ℚ) : ℝ) ≤ stT214 92 := by
  have hc : ((248687/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64818525741/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((248687/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c93 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-46739/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6038937/10000000) (δ := 681/62500000) (ψ := -4983/100000) 214 154
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t93 : ((-48469340003/625000000000 : ℚ) : ℝ) ≤ stT214 93 := by
  have hc : ((-373937/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-48469340003/625000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-373937/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c94 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-401/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24669/62500) (δ := 5407/500000000) (ψ := -4983/100000) 214 155
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t94 : ((-416178777/500000000000 : ℚ) : ℝ) ≤ stT214 94 := by
  have hc : ((-807/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416178777/500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-807/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c95 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((386971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1714383/10000000) (δ := 10789/1000000000) (ψ := -4983/100000) 214 155
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t95 : ((99249520797/1250000000000 : ℚ) : ℝ) ≤ stT214 95 := by
  have hc : ((193473/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99249520797/1250000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((193473/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c96 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-48849/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7316529/10000000) (δ := 5407/500000000) (ψ := -4983/100000) 214 155
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t96 : ((-99717733563/1000000000000 : ℚ) : ℝ) ≤ stT214 96 := by
  have hc : ((-97703/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99717733563/1000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-97703/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c97 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((209281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2847337/10000000) (δ := 10881/1000000000) (ψ := -4983/100000) 214 156
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t97 : ((13279202661/312500000000 : ℚ) : ℝ) ≤ stT214 97 := by
  have hc : ((26157/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13279202661/312500000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((26157/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c98 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((123099/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2639891/10000000) (δ := 5361/500000000) (ψ := -4983/100000) 214 156
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t98 : ((31084018537/625000000000 : ℚ) : ℝ) ≤ stT214 98 := by
  have hc : ((246173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31084018537/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((246173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c99 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-49811/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3818269/5000000) (δ := 10829/1000000000) (ψ := -4983/100000) 214 157
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t99 : ((-50064460413/500000000000 : ℚ) : ℝ) ≤ stT214 99 := by
  have hc : ((-99627/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50064460413/500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-99627/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c100 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((618589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -564907/2500000) (δ := 5387/500000000) (ψ := -4983/100000) 214 157
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t100 : ((618538381461/10000000000000 : ℚ) : ℝ) ≤ stT214 100 := by
  have hc : ((618539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((618538381461/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((618539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c101 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((338443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 765959/2500000) (δ := 5387/500000000) (ψ := -4983/100000) 214 157
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t101 : ((336713555541/10000000000000 : ℚ) : ℝ) ≤ stT214 101 := by
  have hc : ((338393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336713555541/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((338393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c102 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-981561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7373147/10000000) (δ := 10867/1000000000) (ψ := -4983/100000) 214 158
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t102 : ((-242985042107/2500000000000 : ℚ) : ℝ) ≤ stT214 102 := by
  have hc : ((-981611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242985042107/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-981611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c103 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((130267/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2153633/10000000) (δ := 671/62500000) (ψ := -4983/100000) 214 158
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t103 : ((128345999553/2000000000000 : ℚ) : ℝ) ≤ stT214 103 := by
  have hc : ((130257/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128345999553/2000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((130257/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c104 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((356579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3015483/10000000) (δ := 10867/1000000000) (ψ := -4983/100000) 214 158
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t104 : ((17480260341/500000000000 : ℚ) : ℝ) ≤ stT214 104 := by
  have hc : ((356529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17480260341/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((356529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c105 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-993681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7572797/10000000) (δ := 10843/1000000000) (ψ := -4983/100000) 214 159
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t105 : ((-969783076631/10000000000000 : ℚ) : ℝ) ≤ stT214 105 := by
  have hc : ((-993731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-969783076631/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-993731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c106 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((134933/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2501693/10000000) (δ := 269/25000000) (ψ := -4983/100000) 214 159
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t106 : ((52418503137/1000000000000 : ℚ) : ℝ) ≤ stT214 106 := by
  have hc : ((269841/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52418503137/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((269841/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c107 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((532927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50437/200000) (δ := 269/25000000) (ψ := -4983/100000) 214 159
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t107 : ((32196961217/625000000000 : ℚ) : ℝ) ≤ stT214 107 := by
  have hc : ((532877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32196961217/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((532877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c108 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-197983/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3749317/5000000) (δ := 269/25000000) (ψ := -4983/100000) 214 159
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t108 : ((-190518962243/2000000000000 : ℚ) : ℝ) ≤ stT214 108 := by
  have hc : ((-197993/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-190518962243/2000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-197993/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c109 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((256517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204903/625000) (δ := 43/4000000) (ψ := -4983/100000) 214 160
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t109 : ((122825380371/5000000000000 : ℚ) : ℝ) ≤ stT214 109 := by
  have hc : ((256467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122825380371/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((256467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c110 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((160063/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1607439/10000000) (δ := 10853/1000000000) (ψ := -4983/100000) 214 160
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t110 : ((76302226743/1000000000000 : ℚ) : ℝ) ≤ stT214 110 := by
  have hc : ((160053/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76302226743/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((160053/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c111 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-52889/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 403071/625000) (δ := 43/4000000) (ψ := -4983/100000) 214 160
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t111 : ((-200811934323/2500000000000 : ℚ) : ℝ) ≤ stT214 111 := by
  have hc : ((-423137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-200811934323/2500000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-423137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c112 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-211837/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2230313/5000000) (δ := 10857/1000000000) (ψ := -4983/100000) 214 161
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t112 : ((-12513410559/625000000000 : ℚ) : ℝ) ≤ stT214 112 := by
  have hc : ((-211887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12513410559/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-211887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c113 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((993047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294989/10000000) (δ := 10857/1000000000) (ψ := -4983/100000) 214 161
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t113 : ((11676651723/125000000000 : ℚ) : ℝ) ≤ stT214 113 := by
  have hc : ((992997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11676651723/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((992997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c114 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-209647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 250433/500000) (δ := 10857/1000000000) (ψ := -4983/100000) 214 161
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t114 : ((-12273491237/312500000000 : ℚ) : ℝ) ≤ stT214 114 := by
  have hc : ((-26209/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12273491237/312500000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-26209/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c115 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-148917/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3013387/5000000) (δ := 2153/200000000) (ψ := -4983/100000) 214 162
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t115 : ((-27775034427/400000000000 : ℚ) : ℝ) ≤ stT214 115 := by
  have hc : ((-148927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27775034427/400000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-148927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c116 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((84837/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -174343/1250000) (δ := 2153/200000000) (ψ := -4983/100000) 214 162
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t116 : ((615347469/7812500000 : ℚ) : ℝ) ≤ stT214 116 := by
  have hc : ((2651/3125 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((615347469/7812500000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((2651/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c117 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((287639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3197589/10000000) (δ := 2153/200000000) (ψ := -4983/100000) 214 162
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t117 : ((531752061/20000000000 : ℚ) : ℝ) ≤ stT214 117 := by
  have hc : ((287589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((531752061/20000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((287589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c118 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-999149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7750813/10000000) (δ := 5419/500000000) (ψ := -4983/100000) 214 162
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t118 : ((-36793504777/400000000000 : ℚ) : ℝ) ≤ stT214 118 := by
  have hc : ((-999199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36793504777/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-999199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c119 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((48157/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430299/1250000) (δ := 10731/1000000000) (ψ := -4983/100000) 214 163
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t119 : ((44133966861/2500000000000 : ℚ) : ℝ) ≤ stT214 119 := by
  have hc : ((96289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44133966861/2500000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((96289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c120 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((114447/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1034649/10000000) (δ := 1359/125000000) (ψ := -4983/100000) 214 163
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t120 : ((41787810981/500000000000 : ℚ) : ℝ) ≤ stT214 120 := by
  have hc : ((457763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41787810981/500000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((457763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c121 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-290113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5474507/10000000) (δ := 1359/125000000) (ψ := -4983/100000) 214 163
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t121 : ((-131880922279/2500000000000 : ℚ) : ℝ) ≤ stT214 121 := by
  have hc : ((-145069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131880922279/2500000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-145069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c122 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-344917/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5830139/10000000) (δ := 10779/1000000000) (ψ := -4983/100000) 214 164
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t122 : ((-78073999809/1250000000000 : ℚ) : ℝ) ≤ stT214 122 := by
  have hc : ((-172471/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78073999809/1250000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-172471/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c123 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((208413/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -731387/5000000) (δ := 1353/125000000) (ψ := -4983/100000) 214 164
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t123 : ((375816540869/5000000000000 : ℚ) : ℝ) ≤ stT214 123 := by
  have hc : ((416801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375816540869/5000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((416801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c124 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((205297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 717307/2500000) (δ := 1353/125000000) (ψ := -4983/100000) 214 164
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t124 : ((11521224567/312500000000 : ℚ) : ℝ) ≤ stT214 124 := by
  have hc : ((25659/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11521224567/312500000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((25659/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c125 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-481211/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1433291/2000000) (δ := 1353/125000000) (ψ := -4983/100000) 214 164
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t125 : ((-26901934563/312500000000 : ℚ) : ℝ) ≤ stT214 125 := by
  have hc : ((-120309/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26901934563/312500000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-120309/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c126 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-140149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4278521/10000000) (δ := 10717/1000000000) (ψ := -4983/100000) 214 165
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t126 : ((-124899223329/10000000000000 : ℚ) : ℝ) ≤ stT214 126 := by
  have hc : ((-140199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124899223329/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-140199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c127 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((499903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12323/2500000) (δ := 5443/500000000) (ψ := -4983/100000) 214 165
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t127 : ((55446217821/625000000000 : ℚ) : ℝ) ≤ stT214 127 := by
  have hc : ((249939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55446217821/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((249939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c128 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-43909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207341/500000) (δ := 5443/500000000) (ψ := -4983/100000) 214 165
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t128 : ((-4854069957/625000000000 : ℚ) : ℝ) ≤ stT214 128 := by
  have hc : ((-21967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4854069957/625000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-21967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c129 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-245847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7397667/10000000) (δ := 1081/100000000) (ψ := -4983/100000) 214 166
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t129 : ((-432934485269/5000000000000 : ℚ) : ℝ) ≤ stT214 129 := by
  have hc : ((-491719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432934485269/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-491719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c130 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((261173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3266397/10000000) (δ := 1081/100000000) (ψ := -4983/100000) 214 166
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t130 : ((114510008067/5000000000000 : ℚ) : ℝ) ≤ stT214 130 := by
  have hc : ((261123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114510008067/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((261123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c131 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((944967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 166651/2000000) (δ := 10793/1000000000) (ψ := -4983/100000) 214 166
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t131 : ((103197220321/1250000000000 : ℚ) : ℝ) ≤ stT214 131 := by
  have hc : ((944917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103197220321/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((944917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c132 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-380087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1225429/2500000) (δ := 10793/1000000000) (ψ := -4983/100000) 214 166
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t132 : ((-330867063293/10000000000000 : ℚ) : ℝ) ≤ stT214 132 := by
  have hc : ((-380137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330867063293/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-380137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c133 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-907209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1353699/2000000) (δ := 109/10000000) (ψ := -4983/100000) 214 167
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t133 : ((-78669335149/1000000000000 : ℚ) : ℝ) ≤ stT214 133 := by
  have hc : ((-907259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78669335149/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-907259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c134 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((449671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1380499/5000000) (δ := 21503/1000000000) (ψ := -4983/100000) 214 167
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t134 : ((97103298507/2500000000000 : ℚ) : ℝ) ≤ stT214 134 := by
  have hc : ((449621/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97103298507/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((449621/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c135 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((88389/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1216701/10000000) (δ := 109/10000000) (ψ := -4983/100000) 214 167
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t135 : ((594287111/7812500000 : ℚ) : ℝ) ≤ stT214 135 := by
  have hc : ((2762/3125 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594287111/7812500000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((2762/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c136 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-47523/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2582527/5000000) (δ := 10703/1000000000) (ψ := -4983/100000) 214 167
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t136 : ((-5094365913/125000000000 : ℚ) : ℝ) ≤ stT214 136 := by
  have hc : ((-5941/12500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5094365913/125000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-5941/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c137 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-881289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3311723/5000000) (δ := 2159/200000000) (ψ := -4983/100000) 214 168
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t137 : ((-376489512681/5000000000000 : ℚ) : ℝ) ≤ stT214 137 := by
  have hc : ((-881339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376489512681/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-881339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c138 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((91961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2732551/10000000) (δ := 1351/125000000) (ψ := -4983/100000) 214 168
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t138 : ((9784230057/250000000000 : ℚ) : ℝ) ≤ stT214 138 := by
  have hc : ((91951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9784230057/250000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((91951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c139 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((899521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1130309/10000000) (δ := 2159/200000000) (ψ := -4983/100000) 214 168
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t139 : ((190730127137/2500000000000 : ℚ) : ℝ) ≤ stT214 139 := by
  have hc : ((899471/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((190730127137/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((899471/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c140 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-50443/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4965457/10000000) (δ := 1351/125000000) (ψ := -4983/100000) 214 168
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t140 : ((-34109948707/1000000000000 : ℚ) : ℝ) ≤ stT214 140 := by
  have hc : ((-201797/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34109948707/1000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-201797/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c141 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-29161/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3467349/5000000) (δ := 1361/125000000) (ψ := -4983/100000) 214 169
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t141 : ((-49118620669/625000000000 : ℚ) : ℝ) ≤ stT214 141 := by
  have hc : ((-466601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49118620669/625000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-466601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c142 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((30439/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1576873/5000000) (δ := 1361/125000000) (ψ := -4983/100000) 214 169
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t142 : ((12769817277/500000000000 : ℚ) : ℝ) ≤ stT214 142 := by
  have hc : ((15217/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12769817277/500000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((15217/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c143 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((485637/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 60067/1000000) (δ := 1361/125000000) (ψ := -4983/100000) 214 169
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t143 : ((50761143763/625000000000 : ℚ) : ℝ) ≤ stT214 143 := by
  have hc : ((121403/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50761143763/625000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((121403/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c144 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-160061/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4328871/10000000) (δ := 1361/125000000) (ψ := -4983/100000) 214 169
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t144 : ((-66712970037/5000000000000 : ℚ) : ℝ) ≤ stT214 144 := by
  have hc : ((-160111/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66712970037/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-160111/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c145 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-199497/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479789/625000) (δ := 5411/500000000) (ψ := -4983/100000) 214 170
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t145 : ((-33136317137/400000000000 : ℚ) : ℝ) ≤ stT214 145 := by
  have hc : ((-199507/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33136317137/400000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-199507/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c146 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-29049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3999623/10000000) (δ := 10781/1000000000) (ψ := -4983/100000) 214 170
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t146 : ((-12041253497/5000000000000 : ℚ) : ℝ) ≤ stT214 146 := by
  have hc : ((-29099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12041253497/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-29099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c147 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((49517/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -173883/5000000) (δ := 5411/500000000) (ψ := -4983/100000) 214 170
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t147 : ((40838866397/500000000000 : ℚ) : ℝ) ≤ stT214 147 := by
  have hc : ((99029/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).1
  have hw2 : ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((412393/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40838866397/500000000000 : ℚ) : ℝ)
      = ((412393/5000000 : ℚ) : ℝ) * ((99029/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c148 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((1601/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3279373/10000000) (δ := 10781/1000000000) (ψ := -4983/100000) 214 170
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t148 : ((10526044167/500000000000 : ℚ) : ℝ) ≤ stT214 148 := by
  have hc : ((25611/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10526044167/500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((25611/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c149 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-185077/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6882117/10000000) (δ := 5411/500000000) (ψ := -4983/100000) 214 170
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t149 : ((-4738412287/62500000000 : ℚ) : ℝ) ≤ stT214 149 := by
  have hc : ((-185087/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4738412287/62500000000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-185087/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c150 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-125977/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1049457/2000000) (δ := 10729/1000000000) (ψ := -4983/100000) 214 171
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t150 : ((-205740097563/5000000000000 : ℚ) : ℝ) ≤ stT214 150 := by
  have hc : ((-251979/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205740097563/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-251979/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c151 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((31179/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -211553/1250000) (δ := 10729/1000000000) (ψ := -4983/100000) 214 171
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t151 : ((6342867119/100000000000 : ℚ) : ℝ) ≤ stT214 151 := by
  have hc : ((31177/40000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6342867119/100000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((31177/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c152 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((370721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 36779/200000) (δ := 5437/500000000) (ψ := -4983/100000) 214 171
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t152 : ((37584265059/625000000000 : ℚ) : ℝ) ≤ stT214 152 := by
  have hc : ((46337/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37584265059/625000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((46337/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c153 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-134501/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5347159/10000000) (δ := 5437/500000000) (ψ := -4983/100000) 214 171
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t153 : ((-217495685231/5000000000000 : ℚ) : ℝ) ≤ stT214 153 := by
  have hc : ((-269027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217495685231/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-269027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c154 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-924369/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6875439/10000000) (δ := 2709/250000000) (ψ := -4983/100000) 214 172
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t154 : ((-744918091837/10000000000000 : ℚ) : ℝ) ≤ stT214 154 := by
  have hc : ((-924419/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-744918091837/10000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-924419/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c155 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((204287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -853163/2500000) (δ := 10767/1000000000) (ψ := -4983/100000) 214 172
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t155 : ((164047038903/10000000000000 : ℚ) : ℝ) ≤ stT214 155 := by
  have hc : ((204237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164047038903/10000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((204237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c156 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((499969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697/250000) (δ := 2709/250000000) (ψ := -4983/100000) 214 172
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t156 : ((78178743/976562500 : ℚ) : ℝ) ≤ stT214 156 := by
  have hc : ((62493/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78178743/976562500 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((62493/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c157 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((38209/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3446423/10000000) (δ := 2709/250000000) (ψ := -4983/100000) 214 172
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t157 : ((15243043557/1000000000000 : ℚ) : ℝ) ≤ stT214 157 := by
  have hc : ((38199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15243043557/1000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((38199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c158 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-45969/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1368649/2000000) (δ := 2709/250000000) (ψ := -4983/100000) 214 172
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t158 : ((-36572994597/500000000000 : ℚ) : ℝ) ≤ stT214 158 := by
  have hc : ((-91943/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36572994597/500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-91943/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c159 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-292517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5489297/10000000) (δ := 10859/1000000000) (ψ := -4983/100000) 214 173
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t159 : ((-29000127273/625000000000 : ℚ) : ℝ) ≤ stT214 159 := by
  have hc : ((-146271/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29000127273/625000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-146271/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c160 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((328477/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2135061/10000000) (δ := 10859/1000000000) (ψ := -4983/100000) 214 173
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t160 : ((64915992297/1250000000000 : ℚ) : ℝ) ≤ stT214 160 := by
  have hc : ((82113/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64915992297/1250000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((82113/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c161 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((887317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1198257/10000000) (δ := 1343/125000000) (ψ := -4983/100000) 214 173
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t161 : ((69926399537/1000000000000 : ℚ) : ℝ) ≤ stT214 161 := by
  have hc : ((887267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69926399537/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((887267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c162 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-57869/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4510977/10000000) (δ := 1343/125000000) (ψ := -4983/100000) 214 173
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t162 : ((-3638083801/200000000000 : ℚ) : ℝ) ≤ stT214 162 := by
  have hc : ((-115763/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3638083801/200000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-115763/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c163 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-199959/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7803313/10000000) (δ := 10859/1000000000) (ψ := -4983/100000) 214 173
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t163 : ((-156627918909/2000000000000 : ℚ) : ℝ) ≤ stT214 163 := by
  have hc : ((-199969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156627918909/2000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-199969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c164 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-139233/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4632483/10000000) (δ := 21/1953125) (ψ := -4983/100000) 214 174
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t164 : ((-54371127601/2500000000000 : ℚ) : ℝ) ≤ stT214 164 := by
  have hc : ((-69629/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54371127601/2500000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-69629/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c165 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((106429/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690109/5000000) (δ := 21/1953125) (ψ := -4983/100000) 214 174
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t165 : ((165699796059/2500000000000 : ℚ) : ℝ) ≤ stT214 165 := by
  have hc : ((425691/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165699796059/2500000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((425691/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c166 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((737817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1852413/10000000) (δ := 10851/1000000000) (ψ := -4983/100000) 214 174
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t166 : ((11452357141/200000000000 : ℚ) : ℝ) ≤ stT214 166 := by
  have hc : ((737767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11452357141/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((737767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c167 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-27493/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1266419/2500000) (δ := 21/1953125) (ψ := -4983/100000) 214 174
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t167 : ((-2659645179/78125000000 : ℚ) : ℝ) ≤ stT214 167 := by
  have hc : ((-219969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2659645179/78125000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-219969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c168 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-493431/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1862071/2500000) (δ := 2169/200000000) (ψ := -4983/100000) 214 175
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t168 : ((-23794355797/312500000000 : ℚ) : ℝ) ≤ stT214 168 := by
  have hc : ((-30841/31250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23794355797/312500000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-30841/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c169 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-34507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2136583/5000000) (δ := 2169/200000000) (ψ := -4983/100000) 214 175
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t169 : ((-53106939009/5000000000000 : ℚ) : ℝ) ≤ stT214 169 := by
  have hc : ((-69039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53106939009/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-69039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c170 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((112733/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -558413/5000000) (δ := 5379/500000000) (ψ := -4983/100000) 214 175
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t170 : ((86457359087/1250000000000 : ℚ) : ℝ) ≤ stT214 170 := by
  have hc : ((450907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86457359087/1250000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((450907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c171 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((21583/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1010501/5000000) (δ := 2169/200000000) (ψ := -4983/100000) 214 175
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t171 : ((264059764857/5000000000000 : ℚ) : ℝ) ≤ stT214 171 := by
  have hc : ((345303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264059764857/5000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((345303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c172 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-466577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2570267/5000000) (δ := 5379/500000000) (ψ := -4983/100000) 214 175
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t172 : ((-355799821111/10000000000000 : ℚ) : ℝ) ≤ stT214 172 := by
  have hc : ((-466627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-355799821111/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-466627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c173 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-987981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7465981/10000000) (δ := 5369/500000000) (ψ := -4983/100000) 214 176
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t173 : ((-375593068433/5000000000000 : ℚ) : ℝ) ≤ stT214 173 := by
  have hc : ((-988031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-375593068433/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-988031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c174 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-90579/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4382401/10000000) (δ := 2173/200000000) (ψ := -4983/100000) 214 176
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t174 : ((-17171700449/1250000000000 : ℚ) : ℝ) ≤ stT214 174 := by
  have hc : ((-22651/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17171700449/1250000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-22651/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c175 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((432263/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1316477/10000000) (δ := 5369/500000000) (ψ := -4983/100000) 214 176
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t175 : ((20421300429/312500000000 : ℚ) : ℝ) ≤ stT214 175 := by
  have hc : ((216119/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20421300429/312500000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((216119/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c176 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((769473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1731953/10000000) (δ := 5369/500000000) (ψ := -4983/100000) 214 176
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t176 : ((289987065047/5000000000000 : ℚ) : ℝ) ≤ stT214 176 := by
  have hc : ((769423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((289987065047/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((769423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c177 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-65653/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1190789/2500000) (δ := 5369/500000000) (ψ := -4983/100000) 214 176
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t177 : ((-49355396961/2000000000000 : ℚ) : ℝ) ≤ stT214 177 := by
  have hc : ((-65663/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49355396961/2000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-65663/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c178 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-999529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7777239/10000000) (δ := 5369/500000000) (ψ := -4983/100000) 214 176
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t178 : ((-187304111757/2500000000000 : ℚ) : ℝ) ≤ stT214 178 := by
  have hc : ((-999579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187304111757/2500000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-999579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c179 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-391813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2466747/5000000) (δ := 10831/1000000000) (ψ := -4983/100000) 214 177
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t179 : ((-73223128317/2500000000000 : ℚ) : ℝ) ≤ stT214 179 := by
  have hc : ((-391863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73223128317/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-391863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c180 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((710067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1953009/10000000) (δ := 10831/1000000000) (ψ := -4983/100000) 214 177
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t180 : ((105842944207/2000000000000 : ℚ) : ℝ) ≤ stT214 180 := by
  have hc : ((710017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105842944207/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((710017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c181 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((919339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 505499/5000000) (δ := 10831/1000000000) (ψ := -4983/100000) 214 177
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t181 : ((341650998983/5000000000000 : ℚ) : ℝ) ≤ stT214 181 := by
  have hc : ((919289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((341650998983/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((919289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c182 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-12657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1979317/5000000) (δ := 10831/1000000000) (ψ := -4983/100000) 214 177
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t182 : ((-7535251/8000000000 : ℚ) : ℝ) ≤ stT214 182 := by
  have hc : ((-12707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7535251/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-12707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c183 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-926601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6890167/10000000) (δ := 2693/250000000) (ψ := -4983/100000) 214 177
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t183 : ((-342500402761/5000000000000 : ℚ) : ℝ) ≤ stT214 183 := by
  have hc : ((-926651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342500402761/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-926651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c184 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-710429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295113/500000) (δ := 10879/1000000000) (ψ := -4983/100000) 214 178
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t184 : ((-52377222359/1000000000000 : ℚ) : ℝ) ≤ stT214 184 := by
  have hc : ((-710479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52377222359/1000000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-710479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c185 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((361423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3002507/10000000) (δ := 2681/250000000) (ψ := -4983/100000) 214 178
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t185 : ((132843244411/5000000000000 : ℚ) : ℝ) ≤ stT214 185 := by
  have hc : ((361373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132843244411/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((361373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c186 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((499439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118429/10000000) (δ := 2681/250000000) (ψ := -4983/100000) 214 178
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t186 : ((36618782429/500000000000 : ℚ) : ℝ) ≤ stT214 186 := by
  have hc : ((249707/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36618782429/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((249707/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c187 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((45351/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2750241/10000000) (δ := 2681/250000000) (ψ := -4983/100000) 214 178
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t187 : ((2072516257/62500000000 : ℚ) : ℝ) ≤ stT214 187 := by
  have hc : ((22673/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2072516257/62500000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((22673/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c188 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-621477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5603557/10000000) (δ := 10879/1000000000) (ψ := -4983/100000) 214 178
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t188 : ((-18131807171/400000000000 : ℚ) : ℝ) ≤ stT214 188 := by
  have hc : ((-621527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18131807171/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-621527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c189 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-486243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3633089/5000000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 179
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t189 : ((-88426984831/1250000000000 : ℚ) : ℝ) ≤ stT214 189 := by
  have hc : ((-121567/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88426984831/1250000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-121567/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c190 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-40987/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4442983/10000000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 179
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t190 : ((-29742380569/2000000000000 : ℚ) : ℝ) ≤ stT214 190 := by
  have hc : ((-40997/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29742380569/2000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-40997/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c191 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((158753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -817277/5000000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 179
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t191 : ((57431153741/1000000000000 : ℚ) : ℝ) ≤ stT214 191 := by
  have hc : ((158743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57431153741/1000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((158743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c192 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((44721/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 579581/5000000) (δ := 169/15625000) (ψ := -4983/100000) 214 179
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t192 : ((64545520219/1000000000000 : ℚ) : ℝ) ≤ stT214 192 := by
  have hc : ((89437/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64545520219/1000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((89437/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c193 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-1139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196919/500000) (δ := 169/15625000) (ψ := -4983/100000) 214 179
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t193 : ((-207217031/625000000000 : ℚ) : ℝ) ≤ stT214 193 := by
  have hc : ((-2303/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207217031/625000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-2303/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c194 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-223981/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 335163/500000) (δ := 169/15625000) (ψ := -4983/100000) 214 179
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t194 : ((-321636298533/5000000000000 : ℚ) : ℝ) ≤ stT214 194 := by
  have hc : ((-447987/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-321636298533/5000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-447987/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c195 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-802113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3127027/5000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 180
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t195 : ((-114888191349/2000000000000 : ℚ) : ℝ) ≤ stT214 195 := by
  have hc : ((-802163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114888191349/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-802163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c196 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((6523/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140699/400000) (δ := 5447/500000000) (ψ := -4983/100000) 214 180
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t196 : ((931570497/80000000000 : ℚ) : ℝ) ≤ stT214 196 := by
  have hc : ((6521/40000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((931570497/80000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((6521/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c197 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((949887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794807/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 180
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t197 : ((67673036739/1000000000000 : ℚ) : ℝ) ≤ stT214 197 := by
  have hc : ((949837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67673036739/1000000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((949837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c198 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((14419/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1914059/10000000) (δ := 5447/500000000) (ψ := -4983/100000) 214 180
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t198 : ((5123212821/100000000000 : ℚ) : ℝ) ≤ stT214 198 := by
  have hc : ((7209/10000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5123212821/100000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((7209/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c199 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-269541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2304641/5000000) (δ := 5447/500000000) (ψ := -4983/100000) 214 180
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t199 : ((-95554103631/5000000000000 : ℚ) : ℝ) ≤ stT214 199 := by
  have hc : ((-269591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-95554103631/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-269591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c200 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-243687/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7290969/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 180
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t200 : ((-344643244693/5000000000000 : ℚ) : ℝ) ≤ stT214 200 := by
  have hc : ((-487399/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-344643244693/5000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-487399/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c201 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-665867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1437157/2500000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 181
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t201 : ((-234850946141/5000000000000 : ℚ) : ℝ) ≤ stT214 201 := by
  have hc : ((-665917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-234850946141/5000000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-665917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c202 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((163611/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -193349/625000) (δ := 5401/500000000) (ψ := -4983/100000) 214 181
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t202 : ((57549309421/2500000000000 : ℚ) : ℝ) ≤ stT214 202 := by
  have hc : ((81793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57549309421/2500000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((81793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c203 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((983729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -451593/10000000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 181
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t203 : ((345203455149/5000000000000 : ℚ) : ℝ) ≤ stT214 203 := by
  have hc : ((983679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((345203455149/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((983679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c204 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((644093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2177397/10000000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 181
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t204 : ((22546013301/500000000000 : ℚ) : ℝ) ≤ stT214 204 := by
  have hc : ((644043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22546013301/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((644043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c205 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-339723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4793547/10000000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 181
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t205 : ((-237307996163/10000000000000 : ℚ) : ℝ) ≤ stT214 205 := by
  have hc : ((-339773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237307996163/10000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-339773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c206 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-983337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1849241/2500000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 181
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t206 : ((-342579579029/5000000000000 : ℚ) : ℝ) ≤ stT214 206 := by
  have hc : ((-983387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342579579029/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-983387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c207 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-657343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5720209/10000000) (δ := 2179/200000000) (ψ := -4983/100000) 214 182
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t207 : ((-456920347257/10000000000000 : ℚ) : ℝ) ≤ stT214 207 := by
  have hc : ((-657393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-456920347257/10000000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-657393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c208 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((308907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3141883/10000000) (δ := 2677/250000000) (ψ := -4983/100000) 214 182
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t208 : ((1713229779/80000000000 : ℚ) : ℝ) ≤ stT214 208 := by
  have hc : ((308857/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1713229779/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((308857/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c209 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((973583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143979/2500000) (δ := 2677/250000000) (ψ := -4983/100000) 214 182
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t209 : ((336703202781/5000000000000 : ℚ) : ℝ) ≤ stT214 209 := by
  have hc : ((973533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((336703202781/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((973533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c210 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((14061/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1977799/10000000) (δ := 2179/200000000) (ψ := -4983/100000) 214 182
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t210 : ((97023139/2000000000 : ℚ) : ℝ) ≤ stT214 210 := by
  have hc : ((703/1000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97023139/2000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((703/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c211 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-234741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 451937/1000000) (δ := 2179/200000000) (ψ := -4983/100000) 214 182
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t211 : ((-161636933339/10000000000000 : ℚ) : ℝ) ≤ stT214 211 := by
  have hc : ((-234791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161636933339/10000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-234791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c212 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-189719/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 881113/1250000) (δ := 2677/250000000) (ψ := -4983/100000) 214 182
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t212 : ((-130306446387/2000000000000 : ℚ) : ℝ) ≤ stT214 212 := by
  have hc : ((-189729/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130306446387/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-189729/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c213 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-774399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6141403/10000000) (δ := 2697/250000000) (ψ := -4983/100000) 214 183
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t213 : ((-530643935861/10000000000000 : ℚ) : ℝ) ≤ stT214 213 := by
  have hc : ((-774449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-530643935861/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-774449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c214 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((58163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -908879/2500000) (δ := 2163/200000000) (ψ := -4983/100000) 214 183
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t214 : ((3974226473/500000000000 : ℚ) : ℝ) ≤ stT214 214 := by
  have hc : ((29069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3974226473/500000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((29069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c215 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((56099/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -570673/5000000) (δ := 2163/200000000) (ψ := -4983/100000) 214 183
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t215 : ((153028200699/2500000000000 : ℚ) : ℝ) ≤ stT214 215 := by
  have hc : ((448767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153028200699/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((448767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c216 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((859499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 335317/2500000) (δ := 2163/200000000) (ψ := -4983/100000) 214 183
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t216 : ((584780272437/10000000000000 : ℚ) : ℝ) ≤ stT214 216 := by
  have hc : ((859449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((584780272437/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((859449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c217 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((45829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3812379/10000000) (δ := 2697/250000000) (ψ := -4983/100000) 214 183
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t217 : ((7769199869/2500000000000 : ℚ) : ℝ) ≤ stT214 217 := by
  have hc : ((45779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7769199869/2500000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((45779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c218 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-403207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6272149/10000000) (δ := 2163/200000000) (ψ := -4983/100000) 214 183
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t218 : ((-4267240443/78125000000 : ℚ) : ℝ) ≤ stT214 218 := by
  have hc : ((-12601/15625 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4267240443/78125000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-12601/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c219 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-470253/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87341/125000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 184
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t219 : ((-79446178791/1250000000000 : ℚ) : ℝ) ≤ stT214 219 := by
  have hc : ((-235139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).2
  have h0 : (0:ℝ) ≤ ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79446178791/1250000000000 : ℚ) : ℝ)
      = ((337869/5000000 : ℚ) : ℝ) * ((-235139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c220 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-61651/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4549927/10000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 184
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t220 : ((-415735317/25000000000 : ℚ) : ℝ) ≤ stT214 220 := by
  have hc : ((-123327/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415735317/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-123327/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c221 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((132081/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424719/2000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 184
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t221 : ((2776264491/62500000000 : ℚ) : ℝ) ≤ stT214 221 := by
  have hc : ((132071/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2776264491/62500000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((132071/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c222 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((2483/2500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72929/2500000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 184
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t222 : ((3332792907/50000000000 : ℚ) : ℝ) ≤ stT214 222 := by
  have hc : ((19863/20000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).1
  have hw2 : ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((167789/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3332792907/50000000000 : ℚ) : ℝ)
      = ((167789/2500000 : ℚ) : ℝ) * ((19863/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c223 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((472661/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 134811/500000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 184
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t223 : ((316483483539/10000000000000 : ℚ) : ℝ) ≤ stT214 223 := by
  have hc : ((472611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316483483539/10000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((472611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c224 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-224297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508997/1000000) (δ := 17/1562500) (ψ := -4983/100000) 214 184
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t224 : ((-37470410397/1250000000000 : ℚ) : ℝ) ≤ stT214 224 := by
  have hc : ((-112161/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37470410397/1250000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-112161/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c225 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-197683/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3736537/5000000) (δ := 17/1562500) (ψ := -4983/100000) 214 184
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t225 : ((-131795399231/2000000000000 : ℚ) : ℝ) ≤ stT214 225 := by
  have hc : ((-197693/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131795399231/2000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-197693/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c226 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-8739/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1172481/2000000) (δ := 21573/1000000000) (ψ := -4983/100000) 214 185
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t226 : ((-46508159147/1000000000000 : ℚ) : ℝ) ≤ stT214 226 := by
  have hc : ((-69917/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46508159147/1000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-69917/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c227 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((42457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3500353/10000000) (δ := 10773/1000000000) (ψ := -4983/100000) 214 185
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t227 : ((56342781747/5000000000000 : ℚ) : ℝ) ≤ stT214 227 := by
  have hc : ((84889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56342781747/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((84889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c228 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((448141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1148707/10000000) (δ := 10773/1000000000) (ψ := -4983/100000) 214 185
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t228 : ((37096498857/625000000000 : ℚ) : ℝ) ≤ stT214 228 := by
  have hc : ((112029/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37096498857/625000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((112029/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c229 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((444173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1192667/10000000) (δ := 10773/1000000000) (ψ := -4983/100000) 214 185
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t229 : ((36687624133/625000000000 : ℚ) : ℝ) ≤ stT214 229 := by
  have hc : ((111037/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36687624133/625000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((111037/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c230 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((160569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3523823/10000000) (δ := 1083/100000000) (ψ := -4983/100000) 214 185
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t230 : ((5292150911/500000000000 : ℚ) : ℝ) ≤ stT214 230 := by
  have hc : ((160519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5292150911/500000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((160519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c231 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-694087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5844867/10000000) (δ := 1083/100000000) (ψ := -4983/100000) 214 185
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t231 : ((-14272150857/312500000000 : ℚ) : ℝ) ≤ stT214 231 := by
  have hc : ((-694137/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14272150857/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-694137/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c232 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-992719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7552111/10000000) (δ := 5433/500000000) (ψ := -4983/100000) 214 186
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t232 : ((-651785609877/10000000000000 : ℚ) : ℝ) ≤ stT214 232 := by
  have hc : ((-992769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-651785609877/10000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-992769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c233 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-505199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2625511/5000000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 186
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t233 : ((-165499867689/5000000000000 : ℚ) : ℝ) ≤ stT214 233 := by
  have hc : ((-505249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165499867689/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-505249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c234 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((188653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1479889/5000000) (δ := 5433/500000000) (ψ := -4983/100000) 214 186
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t234 : ((770686851/31250000000 : ℚ) : ℝ) ≤ stT214 234 := by
  have hc : ((47157/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((770686851/31250000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((47157/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c235 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((192683/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -169581/2500000) (δ := 5433/500000000) (ψ := -4983/100000) 214 186
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t235 : ((15710749093/250000000000 : ℚ) : ℝ) ≤ stT214 235 := by
  have hc : ((192673/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15710749093/250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((192673/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c236 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((401829/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1593447/10000000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 186
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t236 : ((1021687121/19531250000 : ℚ) : ℝ) ≤ stT214 236 := by
  have hc : ((100451/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1021687121/19531250000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((100451/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c237 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((14279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3855587/10000000) (δ := 5433/500000000) (ψ := -4983/100000) 214 186
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t237 : ((4629478263/2500000000000 : ℚ) : ℝ) ≤ stT214 237 := by
  have hc : ((7127/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4629478263/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((7127/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c238 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-765929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1221641/2000000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 186
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t238 : ((-124127662929/2500000000000 : ℚ) : ℝ) ≤ stT214 238 := by
  have hc : ((-765979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124127662929/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-765979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c239 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-980271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7356557/10000000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 187
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t239 : ((-634117697887/10000000000000 : ℚ) : ℝ) ≤ stT214 239 := by
  have hc : ((-980321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634117697887/10000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-980321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c240 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-460263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2561359/5000000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 187
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t240 : ((-148565560437/5000000000000 : ℚ) : ℝ) ≤ stT214 240 := by
  have hc : ((-460313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-148565560437/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-460313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c241 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((100001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -724547/2500000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 187
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t241 : ((32204096103/1250000000000 : ℚ) : ℝ) ≤ stT214 241 := by
  have hc : ((199977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32204096103/1250000000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((199977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c242 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((60183/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34143/500000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 187
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t242 : ((38685067967/625000000000 : ℚ) : ℝ) ≤ stT214 242 := by
  have hc : ((481439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38685067967/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((481439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c243 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((820033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38083/250000) (δ := 2711/250000000) (ψ := -4983/100000) 214 187
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t243 : ((1052038189/20000000000 : ℚ) : ℝ) ≤ stT214 243 := by
  have hc : ((819983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1052038189/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((819983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c244 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((82519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1860229/5000000) (δ := 2711/250000000) (ψ := -4983/100000) 214 187
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t244 : ((6599416787/1250000000000 : ℚ) : ℝ) ≤ stT214 244 := by
  have hc : ((82469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6599416787/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((82469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c245 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-356103/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5908581/10000000) (δ := 5361/250000000) (ψ := -4983/100000) 214 187
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t245 : ((-7110062133/156250000000 : ℚ) : ℝ) ≤ stT214 245 := by
  have hc : ((-11129/15625 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).2
  have h0 : (0:ℝ) ≤ ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7110062133/156250000000 : ℚ) : ℝ)
      = ((638877/10000000 : ℚ) : ℝ) * ((-11129/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c246 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-995629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381007/500000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 188
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t246 : ((-634822029783/10000000000000 : ℚ) : ℝ) ≤ stT214 246 := by
  have hc : ((-995679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).2
  have h0 : (0:ℝ) ≤ ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-634822029783/10000000000000 : ℚ) : ℝ)
      = ((637577/10000000 : ℚ) : ℝ) * ((-995679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c247 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-572133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -681219/1250000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 188
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t247 : ((-72814292031/2000000000000 : ℚ) : ℝ) ≤ stT214 247 := by
  have hc : ((-572183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72814292031/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-572183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c248 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((252769/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1644069/5000000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 188
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t248 : ((32095313/2000000000 : ℚ) : ℝ) ≤ stT214 248 := by
  have hc : ((252719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32095313/2000000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((252719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c249 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((898657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227049/2000000) (δ := 2713/250000000) (ψ := -4983/100000) 214 188
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t249 : ((142367205617/2500000000000 : ℚ) : ℝ) ≤ stT214 249 := by
  have hc : ((898607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142367205617/2500000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((898607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c250 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((919639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1009089/10000000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 188
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t250 : ((116319732199/2000000000000 : ℚ) : ℝ) ≤ stT214 250 := by
  have hc : ((919589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116319732199/2000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((919589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c251 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((307793/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3144809/10000000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 188
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t251 : ((97122767571/5000000000000 : ℚ) : ℝ) ≤ stT214 251 := by
  have hc : ((307743/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97122767571/5000000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((307743/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c252 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-51243/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2636011/5000000) (δ := 2713/250000000) (ψ := -4983/100000) 214 188
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t252 : ((-2017701023/62500000000 : ℚ) : ℝ) ≤ stT214 252 := by
  have hc : ((-3203/6250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).2
  have h0 : (0:ℝ) ≤ ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2017701023/62500000000 : ℚ) : ℝ)
      = ((629941/10000000 : ℚ) : ℝ) * ((-3203/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c253 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-982889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1847709/2500000) (δ := 2713/250000000) (ψ := -4983/100000) 214 188
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t253 : ((-123593766921/2000000000000 : ℚ) : ℝ) ≤ stT214 253 := by
  have hc : ((-982939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123593766921/2000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-982939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c254 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-98831/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6206659/10000000) (δ := 2149/200000000) (ψ := -4983/100000) 214 189
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t254 : ((-969000399/19531250000 : ℚ) : ℝ) ≤ stT214 254 := by
  have hc : ((-395349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-969000399/19531250000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-395349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c255 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-70937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4104483/10000000) (δ := 5429/500000000) (ψ := -4983/100000) 214 189
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t255 : ((-1778153363/400000000000 : ℚ) : ℝ) ≤ stT214 255 := by
  have hc : ((-70987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).2
  have h0 : (0:ℝ) ≤ ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1778153363/400000000000 : ℚ) : ℝ)
      = ((25049/400000 : ℚ) : ℝ) * ((-70987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c256 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((346837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2010547/10000000) (δ := 2149/200000000) (ψ := -4983/100000) 214 189
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t256 : ((86703/2000000 : ℚ) : ℝ) ≤ stT214 256 := by
  have hc : ((86703/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86703/2000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((86703/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c257 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((249887/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18801/2500000) (δ := 2149/200000000) (ψ := -4983/100000) 214 189
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t257 : ((155867215359/2500000000000 : ℚ) : ℝ) ≤ stT214 257 := by
  have hc : ((499749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).1
  have hw2 : ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((311891/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((155867215359/2500000000000 : ℚ) : ℝ)
      = ((311891/5000000 : ℚ) : ℝ) * ((499749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c258 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((130313/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2152877/10000000) (δ := 5429/500000000) (ψ := -4983/100000) 214 189
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t258 : ((20280749829/500000000000 : ℚ) : ℝ) ≤ stT214 258 := by
  have hc : ((130303/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).1
  have hw2 : ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((155643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20280749829/500000000000 : ℚ) : ℝ)
      = ((155643/2500000 : ℚ) : ℝ) * ((130303/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c259 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-58969/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1055631/2500000) (δ := 2149/200000000) (ψ := -4983/100000) 214 189
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t259 : ((-1832855089/250000000000 : ℚ) : ℝ) ≤ stT214 259 := by
  have hc : ((-29497/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1832855089/250000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-29497/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c260 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-161851/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31421/50000) (δ := 2149/200000000) (ψ := -4983/100000) 214 189
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t260 : ((-50190991907/1000000000000 : ℚ) : ℝ) ≤ stT214 260 := by
  have hc : ((-161861/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).2
  have h0 : (0:ℝ) ≤ ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50190991907/1000000000000 : ℚ) : ℝ)
      = ((310087/5000000 : ℚ) : ℝ) * ((-161861/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c261 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-24533/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1474001/2000000) (δ := 5383/500000000) (ψ := -4983/100000) 214 190
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t261 : ((-12149066189/200000000000 : ℚ) : ℝ) ≤ stT214 261 := by
  have hc : ((-98137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).2
  have h0 : (0:ℝ) ≤ ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12149066189/200000000000 : ℚ) : ℝ)
      = ((123797/2000000 : ℚ) : ℝ) * ((-98137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c262 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-53021/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -332757/625000) (δ := 32237/1000000000) (ψ := -4983/100000) 214 190
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t262 : ((-16379810939/500000000000 : ℚ) : ℝ) ≤ stT214 262 := by
  have hc : ((-26513/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).2
  have h0 : (0:ℝ) ≤ ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16379810939/500000000000 : ℚ) : ℝ)
      = ((617803/10000000 : ℚ) : ℝ) * ((-26513/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c263 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((50717/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3286029/10000000) (δ := 5383/500000000) (ψ := -4983/100000) 214 190
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t263 : ((15633627291/1000000000000 : ℚ) : ℝ) ≤ stT214 263 := by
  have hc : ((50707/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).1
  have hw2 : ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15633627291/1000000000000 : ℚ) : ℝ)
      = ((308313/5000000 : ℚ) : ℝ) * ((50707/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c264 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((876497/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1255651/10000000) (δ := 32237/1000000000) (ψ := -4983/100000) 214 190
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t264 : ((539415441279/10000000000000 : ℚ) : ℝ) ≤ stT214 264 := by
  have hc : ((876447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).1
  have hw2 : ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539415441279/10000000000000 : ℚ) : ℝ)
      = ((615457/10000000 : ℚ) : ℝ) * ((876447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c265 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((476651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47939/625000) (δ := 5383/500000000) (ψ := -4983/100000) 214 190
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t265 : ((29278896867/500000000000 : ℚ) : ℝ) ≤ stT214 265 := by
  have hc : ((238313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29278896867/500000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((238313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c266 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((110529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2782101/10000000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 190
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t266 : ((135523952587/5000000000000 : ℚ) : ℝ) ≤ stT214 266 := by
  have hc : ((221033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((135523952587/5000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((221033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c267 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-338231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2394791/5000000) (δ := 5383/500000000) (ψ := -4983/100000) 214 190
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t267 : ((-207024927471/10000000000000 : ℚ) : ℝ) ≤ stT214 267 := by
  have hc : ((-338281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).2
  have h0 : (0:ℝ) ≤ ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-207024927471/10000000000000 : ℚ) : ℝ)
      = ((611991/10000000 : ℚ) : ℝ) * ((-338281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c268 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-227681/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1697393/2500000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 190
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t268 : ((-8692882443/156250000000 : ℚ) : ℝ) ≤ stT214 268 := by
  have hc : ((-455387/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8692882443/156250000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-455387/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c269 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-29121/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6925837/10000000) (δ := 1073/100000000) (ψ := -4983/100000) 214 191
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t269 : ((-284101547271/5000000000000 : ℚ) : ℝ) ≤ stT214 269 := by
  have hc : ((-465961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284101547271/5000000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-465961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c270 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-394451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2470333/5000000) (δ := 1073/100000000) (ψ := -4983/100000) 214 191
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t270 : ((-240085813081/10000000000000 : ℚ) : ℝ) ≤ stT214 270 := by
  have hc : ((-394501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).2
  have h0 : (0:ℝ) ≤ ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240085813081/10000000000000 : ℚ) : ℝ)
      = ((608581/10000000 : ℚ) : ℝ) * ((-394501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c271 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((376177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -370353/1250000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 191
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t271 : ((7140018841/312500000000 : ℚ) : ℝ) ≤ stT214 271 := by
  have hc : ((376127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7140018841/312500000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((376127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c272 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((461127/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -124039/1250000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 191
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t272 : ((139792062789/2500000000000 : ℚ) : ℝ) ≤ stT214 272 := by
  have hc : ((230551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139792062789/2500000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((230551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c273 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((11569/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970977/10000000) (δ := 1073/100000000) (ψ := -4983/100000) 214 191
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t273 : ((56011943169/1000000000000 : ℚ) : ℝ) ≤ stT214 273 := by
  have hc : ((92547/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).1
  have hw2 : ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((605227/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56011943169/1000000000000 : ℚ) : ℝ)
      = ((605227/10000000 : ℚ) : ℝ) * ((92547/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c274 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((389359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2927151/10000000) (δ := 1073/100000000) (ψ := -4983/100000) 214 191
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t274 : ((117595065849/5000000000000 : ℚ) : ℝ) ≤ stT214 274 := by
  have hc : ((389309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).1
  have hw2 : ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((302061/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117595065849/5000000000000 : ℚ) : ℝ)
      = ((302061/5000000 : ℚ) : ℝ) * ((389309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c275 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-370591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4876103/10000000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 191
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t275 : ((-223505047743/10000000000000 : ℚ) : ℝ) ≤ stT214 275 := by
  have hc : ((-370641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223505047743/10000000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-370641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c276 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-114421/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3409023/5000000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 191
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t276 : ((-27550877837/500000000000 : ℚ) : ℝ) ≤ stT214 276 := by
  have hc : ((-457709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).2
  have h0 : (0:ℝ) ≤ ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27550877837/500000000000 : ℚ) : ℝ)
      = ((60193/1000000 : ℚ) : ℝ) * ((-457709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c277 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-468019/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6954983/10000000) (δ := 539/50000000) (ψ := -4983/100000) 214 192
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t277 : ((-35152561631/625000000000 : ℚ) : ℝ) ≤ stT214 277 := by
  have hc : ((-117011/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).2
  have h0 : (0:ℝ) ≤ ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35152561631/625000000000 : ℚ) : ℝ)
      = ((300421/5000000 : ℚ) : ℝ) * ((-117011/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c278 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-425963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5027057/10000000) (δ := 539/50000000) (ψ := -4983/100000) 214 192
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t278 : ((-255505982893/10000000000000 : ℚ) : ℝ) ≤ stT214 278 := by
  have hc : ((-426013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255505982893/10000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-426013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c279 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((322493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1553043/5000000) (δ := 539/50000000) (ψ := -4983/100000) 214 192
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t279 : ((48260366253/2500000000000 : ℚ) : ℝ) ≤ stT214 279 := by
  have hc : ((322443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).1
  have hw2 : ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149671/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48260366253/2500000000000 : ℚ) : ℝ)
      = ((149671/2500000 : ℚ) : ℝ) * ((322443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c280 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((177697/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -119191/1000000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 192
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t280 : ((53094119409/1000000000000 : ℚ) : ℝ) ≤ stT214 280 := by
  have hc : ((177687/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).1
  have hw2 : ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53094119409/1000000000000 : ℚ) : ℝ)
      = ((298807/5000000 : ℚ) : ℝ) * ((177687/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c281 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((959339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 143073/2000000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 192
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t281 : ((572262893661/10000000000000 : ℚ) : ℝ) ≤ stT214 281 := by
  have hc : ((959289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((572262893661/10000000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((959289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c282 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((250363/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2615899/10000000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 192
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t282 : ((74537012979/2500000000000 : ℚ) : ℝ) ≤ stT214 282 := by
  have hc : ((125169/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74537012979/2500000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((125169/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c283 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-3609/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1127423/2500000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 192
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t283 : ((-68665432207/5000000000000 : ℚ) : ℝ) ≤ stT214 283 := by
  have hc : ((-115513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).2
  have h0 : (0:ℝ) ≤ ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68665432207/5000000000000 : ℚ) : ℝ)
      = ((594439/10000000 : ℚ) : ℝ) * ((-115513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c284 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-52181/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6396851/10000000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 192
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t284 : ((-247724720943/5000000000000 : ℚ) : ℝ) ≤ stT214 284 := by
  have hc : ((-417473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247724720943/5000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-417473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c285 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-985697/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92883/125000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 193
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t285 : ((-583906249703/10000000000000 : ℚ) : ℝ) ≤ stT214 285 := by
  have hc : ((-985747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583906249703/10000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-985747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c286 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-151671/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694587/1250000) (δ := 2679/250000000) (ψ := -4983/100000) 214 193
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t286 : ((-179384850871/5000000000000 : ℚ) : ℝ) ≤ stT214 286 := by
  have hc : ((-303367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).2
  have h0 : (0:ℝ) ≤ ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179384850871/5000000000000 : ℚ) : ℝ)
      = ((591313/10000000 : ℚ) : ℝ) * ((-303367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c287 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((2373/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922333/2500000) (δ := 2679/250000000) (ψ := -4983/100000) 214 193
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t287 : ((5599995847/1000000000000 : ℚ) : ℝ) ≤ stT214 287 := by
  have hc : ((9487/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5599995847/1000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((9487/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c288 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((744241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -365699/2000000) (δ := 2679/250000000) (ψ := -4983/100000) 214 193
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t288 : ((87703653541/2000000000000 : ℚ) : ℝ) ≤ stT214 288 := by
  have hc : ((744191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87703653541/2000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((744191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c289 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((499973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 12961/5000000) (δ := 2679/250000000) (ψ := -4983/100000) 214 193
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t289 : ((14704345589/250000000000 : ℚ) : ℝ) ≤ stT214 289 := by
  have hc : ((124987/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).1
  have hw2 : ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14704345589/250000000000 : ℚ) : ℝ)
      = ((117647/2000000 : ℚ) : ℝ) * ((124987/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c290 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((731969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1873973/10000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 193
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t290 : ((21489873759/500000000000 : ℚ) : ℝ) ≤ stT214 290 := by
  have hc : ((731919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).1
  have hw2 : ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((29361/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21489873759/500000000000 : ℚ) : ℝ)
      = ((29361/500000 : ℚ) : ℝ) * ((731919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c291 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((42227/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3715603/10000000) (δ := 2679/250000000) (ψ := -4983/100000) 214 193
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t291 : ((1236961721/250000000000 : ℚ) : ℝ) ≤ stT214 291 := by
  have hc : ((21101/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).1
  have hw2 : ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((58621/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1236961721/250000000000 : ℚ) : ℝ)
      = ((58621/1000000 : ℚ) : ℝ) * ((21101/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c292 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-604863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2775487/5000000) (δ := 2679/250000000) (ψ := -4983/100000) 214 193
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t292 : ((-176999358539/5000000000000 : ℚ) : ℝ) ≤ stT214 292 := by
  have hc : ((-604913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).2
  have h0 : (0:ℝ) ≤ ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176999358539/5000000000000 : ℚ) : ℝ)
      = ((292603/5000000 : ℚ) : ℝ) * ((-604913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c293 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-982083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 115313/156250) (δ := 2679/250000000) (ψ := -4983/100000) 214 193
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t293 : ((-573768973531/10000000000000 : ℚ) : ℝ) ≤ stT214 293 := by
  have hc : ((-982133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).2
  have h0 : (0:ℝ) ≤ ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-573768973531/10000000000000 : ℚ) : ℝ)
      = ((584207/10000000 : ℚ) : ℝ) * ((-982133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c294 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-171589/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6505133/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 194
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t294 : ((-25019648997/500000000000 : ℚ) : ℝ) ≤ stT214 294 := by
  have hc : ((-171599/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).2
  have h0 : (0:ℝ) ≤ ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25019648997/500000000000 : ℚ) : ℝ)
      = ((145803/2500000 : ℚ) : ℝ) * ((-171599/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c295 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-29991/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4688487/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 194
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t295 : ((-4366090277/250000000000 : ℚ) : ℝ) ≤ stT214 295 := by
  have hc : ((-7499/25000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4366090277/250000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-7499/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c296 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((203697/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2877993/10000000) (δ := 5397/500000000) (ψ := -4983/100000) 214 194
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t296 : ((7398869121/312500000000 : ℚ) : ℝ) ≤ stT214 296 := by
  have hc : ((25459/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).1
  have hw2 : ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7398869121/312500000000 : ℚ) : ℝ)
      = ((290619/5000000 : ℚ) : ℝ) * ((25459/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c297 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((909199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1073599/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 194
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t297 : ((263770490221/5000000000000 : ℚ) : ℝ) ≤ stT214 297 := by
  have hc : ((909149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).1
  have hw2 : ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290129/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263770490221/5000000000000 : ℚ) : ℝ)
      = ((290129/5000000 : ℚ) : ℝ) * ((909149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c298 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((958279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724697/10000000) (δ := 5397/500000000) (ψ := -4983/100000) 214 194
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t298 : ((138771682009/2500000000000 : ℚ) : ℝ) ≤ stT214 298 := by
  have hc : ((958229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138771682009/2500000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((958229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c299 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((66821/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2517/10000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 194
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t299 : ((77279810663/2500000000000 : ℚ) : ℝ) ≤ stT214 299 := by
  have hc : ((267259/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77279810663/2500000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((267259/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c300 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-149961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 268957/625000) (δ := 5397/500000000) (ψ := -4983/100000) 214 194
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t300 : ((-86609000861/10000000000000 : ℚ) : ℝ) ≤ stT214 300 := by
  have hc : ((-150011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).2
  have h0 : (0:ℝ) ≤ ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86609000861/10000000000000 : ℚ) : ℝ)
      = ((577351/10000000 : ℚ) : ℝ) * ((-150011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c301 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-759587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1216737/2000000) (δ := 5397/500000000) (ψ := -4983/100000) 214 194
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t301 : ((-437847930067/10000000000000 : ℚ) : ℝ) ≤ stT214 301 := by
  have hc : ((-759637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-437847930067/10000000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-759637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c302 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7849791/10000000) (δ := 10901/1000000000) (ψ := -4983/100000) 214 195
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t302 : ((-143866049091/2500000000000 : ℚ) : ℝ) ≤ stT214 302 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-143866049091/2500000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c303 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-758937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1520297/2500000) (δ := 10901/1000000000) (ψ := -4983/100000) 214 195
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t303 : ((-87205329339/2000000000000 : ℚ) : ℝ) ≤ stT214 303 := by
  have hc : ((-758987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87205329339/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-758987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c304 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-155931/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269901/625000) (δ := 5351/500000000) (ψ := -4983/100000) 214 195
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t304 : ((-4473067137/500000000000 : ℚ) : ℝ) ≤ stT214 304 := by
  have hc : ((-155981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).2
  have h0 : (0:ℝ) ≤ ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4473067137/500000000000 : ℚ) : ℝ)
      = ((28677/500000 : ℚ) : ℝ) * ((-155981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c305 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((519449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -640369/2500000) (δ := 5351/500000000) (ψ := -4983/100000) 214 195
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t305 : ((148703414301/5000000000000 : ℚ) : ℝ) ≤ stT214 305 := by
  have hc : ((519399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148703414301/5000000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((519399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c306 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((947943/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -810207/10000000) (δ := 5351/500000000) (ψ := -4983/100000) 214 195
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t306 : ((541873460273/10000000000000 : ℚ) : ℝ) ≤ stT214 306 := by
  have hc : ((947893/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((541873460273/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((947893/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c307 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((58177/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 233821/2500000) (δ := 5351/500000000) (ψ := -4983/100000) 214 195
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t307 : ((26561260543/500000000000 : ℚ) : ℝ) ≤ stT214 307 := by
  have hc : ((465391/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).1
  have hw2 : ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57073/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26561260543/500000000000 : ℚ) : ℝ)
      = ((57073/1000000 : ℚ) : ℝ) * ((465391/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c308 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((60011/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83597/312500) (δ := 5351/500000000) (ψ := -4983/100000) 214 195
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t308 : ((68381653119/2500000000000 : ℚ) : ℝ) ≤ stT214 308 := by
  have hc : ((240019/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).1
  have hw2 : ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((284901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68381653119/2500000000000 : ℚ) : ℝ)
      = ((284901/5000000 : ℚ) : ℝ) * ((240019/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c309 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-191731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2204653/5000000) (δ := 10901/1000000000) (ψ := -4983/100000) 214 195
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t309 : ((-109100567061/10000000000000 : ℚ) : ℝ) ≤ stT214 309 := by
  have hc : ((-191781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109100567061/10000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-191781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c310 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-77351/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6137891/10000000) (δ := 10901/1000000000) (ψ := -4983/100000) 214 195
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t310 : ((-5491908559/125000000000 : ℚ) : ℝ) ≤ stT214 310 := by
  have hc : ((-19339/25000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).2
  have h0 : (0:ℝ) ≤ ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5491908559/125000000000 : ℚ) : ℝ)
      = ((283981/5000000 : ℚ) : ℝ) * ((-19339/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c311 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-249999/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7846997/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t311 : ((-35442130263/625000000000 : ℚ) : ℝ) ≤ stT214 311 := by
  have hc : ((-500023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).2
  have h0 : (0:ℝ) ≤ ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35442130263/625000000000 : ℚ) : ℝ)
      = ((70881/1250000 : ℚ) : ℝ) * ((-500023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c312 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-192847/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -306477/500000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t312 : ((-218370568941/5000000000000 : ℚ) : ℝ) ≤ stT214 312 := by
  have hc : ((-385719/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).2
  have h0 : (0:ℝ) ≤ ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218370568941/5000000000000 : ℚ) : ℝ)
      = ((566139/10000000 : ℚ) : ℝ) * ((-385719/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c313 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-194963/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220877/500000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t313 : ((-55113989021/5000000000000 : ℚ) : ℝ) ≤ stT214 313 := by
  have hc : ((-195013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55113989021/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-195013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c314 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((116861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2710997/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t314 : ((32970673851/1250000000000 : ℚ) : ℝ) ≤ stT214 314 := by
  have hc : ((233697/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).1
  have hw2 : ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141083/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32970673851/1250000000000 : ℚ) : ℝ)
      = ((141083/2500000 : ℚ) : ℝ) * ((233697/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c315 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((459759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -504929/5000000) (δ := 5397/500000000) (ψ := -4983/100000) 214 196
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t315 : ((32378835753/625000000000 : ℚ) : ℝ) ≤ stT214 315 := by
  have hc : ((229867/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).1
  have hw2 : ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140859/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32378835753/625000000000 : ℚ) : ℝ)
      = ((140859/2500000 : ℚ) : ℝ) * ((229867/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c316 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((962601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 342939/5000000) (δ := 5397/500000000) (ψ := -4983/100000) 214 196
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t316 : ((541476327193/10000000000000 : ℚ) : ℝ) ≤ stT214 316 := by
  have hc : ((962551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((541476327193/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((962551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c317 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((581289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2376211/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t317 : ((65291158109/2000000000000 : ℚ) : ℝ) ≤ stT214 317 := by
  have hc : ((581239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65291158109/2000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((581239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c318 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-53677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4061247/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t318 : ((-30128650971/10000000000000 : ℚ) : ℝ) ≤ stT214 318 := by
  have hc : ((-53727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).2
  have h0 : (0:ℝ) ≤ ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30128650971/10000000000000 : ℚ) : ℝ)
      = ((560773/10000000 : ℚ) : ℝ) * ((-53727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c319 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-663599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71763/125000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t319 : ((-371572429557/10000000000000 : ℚ) : ℝ) ≤ stT214 319 := by
  have hc : ((-663649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-371572429557/10000000000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-663649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c320 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-984657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7415483/10000000) (δ := 10809/1000000000) (ψ := -4983/100000) 214 196
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t320 : ((-550467953019/10000000000000 : ℚ) : ℝ) ≤ stT214 320 := by
  have hc : ((-984707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-550467953019/10000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-984707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c321 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-881237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3311587/5000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t321 : ((-245943406951/5000000000000 : ℚ) : ℝ) ≤ stT214 321 := by
  have hc : ((-881287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-245943406951/5000000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-881287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c322 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-401219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -495911/1000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t322 : ((-223618787051/10000000000000 : ℚ) : ℝ) ≤ stT214 322 := by
  have hc : ((-401269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).2
  have h0 : (0:ℝ) ≤ ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-223618787051/10000000000000 : ℚ) : ℝ)
      = ((557279/10000000 : ℚ) : ℝ) * ((-401269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c323 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((49621/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1650091/5000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t323 : ((13802127477/1000000000000 : ℚ) : ℝ) ≤ stT214 323 := by
  have hc : ((49611/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13802127477/1000000000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((49611/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c324 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((790877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -164639/1000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t324 : ((87869578797/2000000000000 : ℚ) : ℝ) ≤ stT214 324 := by
  have hc : ((790827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87869578797/2000000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((790827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c325 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1133/5000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t325 : ((110934453/2000000000 : ℚ) : ℝ) ≤ stT214 325 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).1
  have hw2 : ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110934453/2000000000 : ℚ) : ℝ)
      = ((5547/100000 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c326 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((395499/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1645893/10000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t326 : ((13689530247/312500000000 : ℚ) : ℝ) ≤ stT214 326 := by
  have hc : ((197737/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).1
  have hw2 : ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69231/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13689530247/312500000000 : ℚ) : ℝ)
      = ((69231/1250000 : ℚ) : ℝ) * ((197737/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c327 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((12709/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3284491/10000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t327 : ((14053414413/1000000000000 : ℚ) : ℝ) ≤ stT214 327 := by
  have hc : ((25413/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).1
  have hw2 : ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((553001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14053414413/1000000000000 : ℚ) : ℝ)
      = ((553001/10000000 : ℚ) : ℝ) * ((25413/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c328 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-77229/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2459057/5000000) (δ := 2679/250000000) (ψ := -4983/100000) 214 197
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t328 : ((-21324065881/1000000000000 : ℚ) : ℝ) ≤ stT214 328 := by
  have hc : ((-77239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).2
  have h0 : (0:ℝ) ≤ ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21324065881/1000000000000 : ℚ) : ℝ)
      = ((276079/5000000 : ℚ) : ℝ) * ((-77239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c329 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-86637/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6546707/10000000) (δ := 10887/1000000000) (ψ := -4983/100000) 214 197
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t329 : ((-11941823539/250000000000 : ℚ) : ℝ) ≤ stT214 329 := by
  have hc : ((-43321/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).2
  have h0 : (0:ℝ) ≤ ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11941823539/250000000000 : ℚ) : ℝ)
      = ((275659/5000000 : ℚ) : ℝ) * ((-43321/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c330 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-496001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471099/625000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 198
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t330 : ((-68263346133/1250000000000 : ℚ) : ℝ) ≤ stT214 330 := by
  have hc : ((-248013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).2
  have h0 : (0:ℝ) ≤ ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68263346133/1250000000000 : ℚ) : ℝ)
      = ((275241/5000000 : ℚ) : ℝ) * ((-248013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c331 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-715079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1183767/2000000) (δ := 539/50000000) (ψ := -4983/100000) 214 198
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t331 : ((-7861413097/200000000000 : ℚ) : ℝ) ≤ stT214 331 := by
  have hc : ((-715129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7861413097/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-715129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c332 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-15061/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2152477/5000000) (δ := 539/50000000) (ψ := -4983/100000) 214 198
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t332 : ((-2067138063/250000000000 : ℚ) : ℝ) ≤ stT214 332 := by
  have hc : ((-7533/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2067138063/250000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-7533/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c333 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((11819/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2695941/10000000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 198
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t333 : ((6476079729/250000000000 : ℚ) : ℝ) ≤ stT214 333 := by
  have hc : ((47271/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).1
  have hw2 : ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136999/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6476079729/250000000000 : ℚ) : ℝ)
      = ((136999/2500000 : ℚ) : ℝ) * ((47271/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c334 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((906153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34117/312500) (δ := 539/50000000) (ψ := -4983/100000) 214 198
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t334 : ((19831876361/400000000000 : ℚ) : ℝ) ≤ stT214 334 := by
  have hc : ((906103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).1
  have hw2 : ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21887/400000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19831876361/400000000000 : ℚ) : ℝ)
      = ((21887/400000 : ℚ) : ℝ) * ((906103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c335 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((979451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 126923/2500000) (δ := 539/50000000) (ψ := -4983/100000) 214 198
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t335 : ((267551785779/5000000000000 : ℚ) : ℝ) ≤ stT214 335 := by
  have hc : ((979401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267551785779/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((979401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c336 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((333387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2102313/10000000) (δ := 539/50000000) (ψ := -4983/100000) 214 198
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t336 : ((11366477433/312500000000 : ℚ) : ℝ) ≤ stT214 336 := by
  have hc : ((166681/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11366477433/312500000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((166681/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c337 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((11721/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1846113/5000000) (δ := 539/50000000) (ψ := -4983/100000) 214 198
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t337 : ((12762845253/2500000000000 : ℚ) : ℝ) ≤ stT214 337 := by
  have hc : ((46859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12762845253/2500000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((46859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c338 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-514269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2638689/5000000) (δ := 10823/1000000000) (ψ := -4983/100000) 214 198
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t338 : ((-279753019351/10000000000000 : ℚ) : ℝ) ≤ stT214 338 := by
  have hc : ((-514319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279753019351/10000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-514319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c339 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-36867/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 857241/1250000) (δ := 539/50000000) (ψ := -4983/100000) 214 198
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t339 : ((-10012256247/200000000000 : ℚ) : ℝ) ≤ stT214 339 := by
  have hc : ((-36869/40000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10012256247/200000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-36869/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c340 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-243307/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7274193/10000000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 199
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t340 : ((-263917468953/5000000000000 : ℚ) : ℝ) ≤ stT214 340 := by
  have hc : ((-486639/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263917468953/5000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-486639/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c341 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-652141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1140601/2000000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 199
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t341 : ((-353181644421/10000000000000 : ℚ) : ℝ) ≤ stT214 341 := by
  have hc : ((-652191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).2
  have h0 : (0:ℝ) ≤ ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353181644421/10000000000000 : ℚ) : ℝ)
      = ((541531/10000000 : ℚ) : ℝ) * ((-652191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c342 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-83651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1034091/2500000) (δ := 1073/100000000) (ψ := -4983/100000) 214 199
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t342 : ((-45260395039/10000000000000 : ℚ) : ℝ) ≤ stT214 342 := by
  have hc : ((-83701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).2
  have h0 : (0:ℝ) ≤ ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45260395039/10000000000000 : ℚ) : ℝ)
      = ((540739/10000000 : ℚ) : ℝ) * ((-83701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c343 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((10301/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -102973/400000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 199
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t343 : ((55614747/2000000000 : ℚ) : ℝ) ≤ stT214 343 := by
  have hc : ((103/200 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55614747/2000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((103/200 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c344 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((459209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1016833/10000000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 199
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t344 : ((15473438937/312500000000 : ℚ) : ℝ) ≤ stT214 344 := by
  have hc : ((28699/31250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15473438937/312500000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((28699/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c345 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((97709/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 107233/2000000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 199
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t345 : ((6575247153/125000000000 : ℚ) : ℝ) ≤ stT214 345 := by
  have hc : ((12213/12500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).1
  have hw2 : ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((538381/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6575247153/125000000000 : ℚ) : ℝ)
      = ((538381/10000000 : ℚ) : ℝ) * ((12213/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c346 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((21001/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260577/1250000) (δ := 1073/100000000) (ψ := -4983/100000) 214 199
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t346 : ((180629769573/5000000000000 : ℚ) : ℝ) ≤ stT214 346 := by
  have hc : ((335991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).1
  have hw2 : ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((537603/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180629769573/5000000000000 : ℚ) : ℝ)
      = ((537603/10000000 : ℚ) : ℝ) * ((335991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c347 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((119063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1814313/5000000) (δ := 1073/100000000) (ψ := -4983/100000) 214 199
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t347 : ((15972377691/2500000000000 : ℚ) : ℝ) ≤ stT214 347 := by
  have hc : ((119013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).1
  have hw2 : ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((134207/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15972377691/2500000000000 : ℚ) : ℝ)
      = ((134207/2500000 : ℚ) : ℝ) * ((119013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c348 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-95267/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1033639/2000000) (δ := 10873/1000000000) (ψ := -4983/100000) 214 199
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t348 : ((-51073902789/2000000000000 : ℚ) : ℝ) ≤ stT214 348 := by
  have hc : ((-95277/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).2
  have h0 : (0:ℝ) ≤ ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51073902789/2000000000000 : ℚ) : ℝ)
      = ((536057/10000000 : ℚ) : ℝ) * ((-95277/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c349 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-179189/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3351689/5000000) (δ := 1073/100000000) (ψ := -4983/100000) 214 199
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t349 : ((-11990384289/250000000000 : ℚ) : ℝ) ≤ stT214 349 := by
  have hc : ((-179199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).2
  have h0 : (0:ℝ) ≤ ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11990384289/250000000000 : ℚ) : ℝ)
      = ((66911/1250000 : ℚ) : ℝ) * ((-179199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c350 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-494231/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7473843/10000000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t350 : ((-16511949993/312500000000 : ℚ) : ℝ) ≤ stT214 350 := by
  have hc : ((-30891/31250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).2
  have h0 : (0:ℝ) ≤ ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16511949993/312500000000 : ℚ) : ℝ)
      = ((534523/10000000 : ℚ) : ℝ) * ((-30891/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c351 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-723029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1189487/2000000) (δ := 5383/500000000) (ψ := -4983/100000) 214 200
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t351 : ((-385951370119/10000000000000 : ℚ) : ℝ) ≤ stT214 351 := by
  have hc : ((-723079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-385951370119/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-723079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c352 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-198051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4425413/10000000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t352 : ((-52794114601/5000000000000 : ℚ) : ℝ) ≤ stT214 352 := by
  have hc : ((-198101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52794114601/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-198101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c353 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((99131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -363459/1250000) (δ := 5383/500000000) (ψ := -4983/100000) 214 200
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t353 : ((52755425151/2500000000000 : ℚ) : ℝ) ≤ stT214 353 := by
  have hc : ((198237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).1
  have hw2 : ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((266123/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52755425151/2500000000000 : ℚ) : ℝ)
      = ((266123/5000000 : ℚ) : ℝ) * ((198237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c354 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((848483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139421/1000000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t354 : ((225468524451/5000000000000 : ℚ) : ℝ) ≤ stT214 354 := by
  have hc : ((848433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).1
  have hw2 : ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((265747/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((225468524451/5000000000000 : ℚ) : ℝ)
      = ((265747/5000000 : ℚ) : ℝ) * ((848433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c355 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((31217/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57459/5000000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t355 : ((33134812321/625000000000 : ℚ) : ℝ) ≤ stT214 355 := by
  have hc : ((499447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33134812321/625000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((499447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c356 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((797323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1619873/10000000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t356 : ((211276547727/5000000000000 : ℚ) : ℝ) ≤ stT214 356 := by
  have hc : ((797273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211276547727/5000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((797273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c357 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((79253/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 780137/2500000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t357 : ((10484627517/625000000000 : ℚ) : ℝ) ≤ stT214 357 := by
  have hc : ((158481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10484627517/625000000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((158481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c358 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-68133/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 92341/200000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t358 : ((-72032110447/5000000000000 : ℚ) : ℝ) ≤ stT214 358 := by
  have hc : ((-136291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72032110447/5000000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-136291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c359 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-766231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6109379/10000000) (δ := 10837/1000000000) (ψ := -4983/100000) 214 200
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t359 : ((-20221389309/500000000000 : ℚ) : ℝ) ≤ stT214 359 := by
  have hc : ((-766281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20221389309/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-766281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c360 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-497373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1899397/2500000) (δ := 5383/500000000) (ψ := -4983/100000) 214 200
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t360 : ((-131076061853/2500000000000 : ℚ) : ℝ) ≤ stT214 360 := by
  have hc : ((-248699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131076061853/2500000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-248699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c361 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-176367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6626339/10000000) (δ := 5429/500000000) (ψ := -4983/100000) 214 201
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t361 : ((-23207509283/500000000000 : ℚ) : ℝ) ≤ stT214 361 := by
  have hc : ((-176377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23207509283/500000000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-176377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c362 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-2929/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40206/78125) (δ := 2149/200000000) (ψ := -4983/100000) 214 201
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t362 : ((-24633830841/1000000000000 : ℚ) : ℝ) ≤ stT214 362 := by
  have hc : ((-46869/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).2
  have h0 : (0:ℝ) ≤ ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24633830841/1000000000000 : ℚ) : ℝ)
      = ((525589/10000000 : ℚ) : ℝ) * ((-46869/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c363 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((10241/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3670517/10000000) (δ := 2149/200000000) (ψ := -4983/100000) 214 201
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t363 : ((1343124417/250000000000 : ℚ) : ℝ) ≤ stT214 363 := by
  have hc : ((2559/25000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1343124417/250000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((2559/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c364 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((318771/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -549683/2500000) (δ := 2149/200000000) (ψ := -4983/100000) 214 201
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t364 : ((41767041483/1250000000000 : ℚ) : ℝ) ≤ stT214 364 := by
  have hc : ((159373/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41767041483/1250000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((159373/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c365 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((957559/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9137/125000) (δ := 5429/500000000) (ψ := -4983/100000) 214 201
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t365 : ((501182233307/10000000000000 : ℚ) : ℝ) ≤ stT214 365 := by
  have hc : ((957509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).1
  have hw2 : ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((523423/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((501182233307/10000000000000 : ℚ) : ℝ)
      = ((523423/10000000 : ℚ) : ℝ) * ((957509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c366 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((957347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229/3125) (δ := 5429/500000000) (ψ := -4983/100000) 214 201
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t366 : ((125096700069/2500000000000 : ℚ) : ℝ) ≤ stT214 366 := by
  have hc : ((957297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).1
  have hw2 : ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((130677/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125096700069/2500000000000 : ℚ) : ℝ)
      = ((130677/2500000 : ℚ) : ℝ) * ((957297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c367 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((319723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548137/2500000) (δ := 2149/200000000) (ψ := -4983/100000) 214 201
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t367 : ((16688075751/500000000000 : ℚ) : ℝ) ≤ stT214 367 := by
  have hc : ((159849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).1
  have hw2 : ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((104399/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16688075751/500000000000 : ℚ) : ℝ)
      = ((104399/2000000 : ℚ) : ℝ) * ((159849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c368 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((111231/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 228021/625000) (δ := 5429/500000000) (ψ := -4983/100000) 214 201
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t368 : ((28978549383/5000000000000 : ℚ) : ℝ) ≤ stT214 368 := by
  have hc : ((111181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).1
  have hw2 : ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28978549383/5000000000000 : ℚ) : ℝ)
      = ((260643/5000000 : ℚ) : ℝ) * ((111181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c369 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-90447/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2550083/5000000) (δ := 2149/200000000) (ψ := -4983/100000) 214 201
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t369 : ((-2354505253/100000000000 : ℚ) : ℝ) ≤ stT214 369 := by
  have hc : ((-90457/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).2
  have h0 : (0:ℝ) ≤ ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2354505253/100000000000 : ℚ) : ℝ)
      = ((26029/500000 : ℚ) : ℝ) * ((-90457/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c370 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-433323/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 654809/1000000) (δ := 2149/200000000) (ψ := -4983/100000) 214 201
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t370 : ((-14080451553/312500000000 : ℚ) : ℝ) ≤ stT214 370 := by
  have hc : ((-108337/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).2
  have h0 : (0:ℝ) ≤ ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14080451553/312500000000 : ℚ) : ℝ)
      = ((129969/2500000 : ℚ) : ℝ) * ((-108337/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c371 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-39939/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1928977/2500000) (δ := 2713/250000000) (ψ := -4983/100000) 214 202
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t371 : ((-829454747/16000000000 : ℚ) : ℝ) ≤ stT214 371 := by
  have hc : ((-39941/40000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).2
  have h0 : (0:ℝ) ≤ ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-829454747/16000000000 : ℚ) : ℝ)
      = ((20767/400000 : ℚ) : ℝ) * ((-39941/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c372 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-201819/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1255159/2000000) (δ := 2713/250000000) (ψ := -4983/100000) 214 202
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t372 : ((-52322394397/1250000000000 : ℚ) : ℝ) ≤ stT214 372 := by
  have hc : ((-403663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52322394397/1250000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-403663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c373 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-71393/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2419767/5000000) (δ := 2713/250000000) (ψ := -4983/100000) 214 202
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t373 : ((-36971116743/2000000000000 : ℚ) : ℝ) ≤ stT214 373 := by
  have hc : ((-71403/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36971116743/2000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-71403/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c374 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((20643/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3407179/10000000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 202
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t374 : ((5335820753/500000000000 : ℚ) : ℝ) ≤ stT214 374 := by
  have hc : ((10319/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).1
  have hw2 : ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((517087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5335820753/500000000000 : ℚ) : ℝ)
      = ((517087/10000000 : ℚ) : ℝ) * ((10319/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c375 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((702831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247321/1250000) (δ := 2713/250000000) (ψ := -4983/100000) 214 202
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t375 : ((362914000057/10000000000000 : ℚ) : ℝ) ≤ stT214 375 := by
  have hc : ((702781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).1
  have hw2 : ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((516397/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362914000057/10000000000000 : ℚ) : ℝ)
      = ((516397/10000000 : ℚ) : ℝ) * ((702781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c376 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((243891/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55381/1000000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 202
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t376 : ((25154116247/500000000000 : ℚ) : ℝ) ≤ stT214 376 := by
  have hc : ((487757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25154116247/500000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((487757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c377 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((188089/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17343/200000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 202
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t377 : ((48432787527/1000000000000 : ℚ) : ℝ) ≤ stT214 377 := by
  have hc : ((188079/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48432787527/1000000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((188079/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c378 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((19087/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 456873/2000000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 202
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t378 : ((19632960531/625000000000 : ℚ) : ℝ) ≤ stT214 378 := by
  have hc : ((305367/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19632960531/625000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((305367/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c379 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((91513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3697889/10000000) (δ := 2713/250000000) (ψ := -4983/100000) 214 202
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t379 : ((9396268379/2000000000000 : ℚ) : ℝ) ≤ stT214 379 := by
  have hc : ((91463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9396268379/2000000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((91463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c380 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-454891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2553807/5000000) (δ := 2713/250000000) (ψ := -4983/100000) 214 202
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t380 : ((-23338018359/1000000000000 : ℚ) : ℝ) ≤ stT214 380 := by
  have hc : ((-454941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23338018359/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-454941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c381 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-85969/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6513647/10000000) (δ := 10751/1000000000) (ψ := -4983/100000) 214 202
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t381 : ((-5505731973/125000000000 : ℚ) : ℝ) ≤ stT214 381 := by
  have hc : ((-42987/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5505731973/125000000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-42987/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c382 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-249923/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7791921/10000000) (δ := 2711/250000000) (ψ := -4983/100000) 214 203
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t382 : ((-51151299559/1000000000000 : ℚ) : ℝ) ≤ stT214 382 := by
  have hc : ((-499871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51151299559/1000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-499871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c383 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-834107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -639327/1000000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t383 : ((-426235041389/10000000000000 : ℚ) : ℝ) ≤ stT214 383 := by
  have hc : ((-834157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).2
  have h0 : (0:ℝ) ≤ ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426235041389/10000000000000 : ℚ) : ℝ)
      = ((510977/10000000 : ℚ) : ℝ) * ((-834157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c384 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-415493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1249551/2500000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t384 : ((-212056163873/10000000000000 : ℚ) : ℝ) ≤ stT214 384 := by
  have hc : ((-415543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).2
  have h0 : (0:ℝ) ≤ ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212056163873/10000000000000 : ℚ) : ℝ)
      = ((510311/10000000 : ℚ) : ℝ) * ((-415543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c385 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((15967/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -450847/1250000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t385 : ((32537393421/5000000000000 : ℚ) : ℝ) ≤ stT214 385 := by
  have hc : ((63843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32537393421/5000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((63843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c386 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((7891/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1109493/5000000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t386 : ((16064361639/500000000000 : ℚ) : ℝ) ≤ stT214 386 := by
  have hc : ((63123/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16064361639/500000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((63123/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c387 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((944767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834781/10000000) (δ := 2711/250000000) (ψ := -4983/100000) 214 203
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t387 : ((60028262897/1250000000000 : ℚ) : ℝ) ≤ stT214 387 := by
  have hc : ((944717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).1
  have hw2 : ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((63541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60028262897/1250000000000 : ℚ) : ℝ)
      = ((63541/1250000 : ℚ) : ℝ) * ((944717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c388 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((195251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 272947/5000000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t388 : ((99118584193/2000000000000 : ℚ) : ℝ) ≤ stT214 388 := by
  have hc : ((195241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).1
  have hw2 : ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99118584193/2000000000000 : ℚ) : ℝ)
      = ((507673/10000000 : ℚ) : ℝ) * ((195241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c389 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((89809/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 240373/1250000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t389 : ((9106358061/250000000000 : ℚ) : ℝ) ≤ stT214 389 := by
  have hc : ((359211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).1
  have hw2 : ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((25351/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9106358061/250000000000 : ℚ) : ℝ)
      = ((25351/500000 : ℚ) : ℝ) * ((359211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c390 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((49903/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3296543/10000000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t390 : ((25264268517/2000000000000 : ℚ) : ℝ) ≤ stT214 390 := by
  have hc : ((49893/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).1
  have hw2 : ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((506369/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25264268517/2000000000000 : ℚ) : ℝ)
      = ((506369/10000000 : ℚ) : ℝ) * ((49893/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c391 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-18221/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4666571/10000000) (δ := 10759/1000000000) (ψ := -4983/100000) 214 203
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t391 : ((-36865363773/2500000000000 : ℚ) : ℝ) ≤ stT214 391 := by
  have hc : ((-145793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).2
  have h0 : (0:ℝ) ≤ ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36865363773/2500000000000 : ℚ) : ℝ)
      = ((252861/5000000 : ℚ) : ℝ) * ((-145793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c392 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-373139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6033121/10000000) (δ := 2711/250000000) (ψ := -4983/100000) 214 203
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t392 : ((-47119138407/1250000000000 : ℚ) : ℝ) ≤ stT214 392 := by
  have hc : ((-93291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).2
  have h0 : (0:ℝ) ≤ ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47119138407/1250000000000 : ℚ) : ℝ)
      = ((505077/10000000 : ℚ) : ℝ) * ((-93291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c393 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-983281/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3698097/5000000) (δ := 2711/250000000) (ψ := -4983/100000) 214 203
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t393 : ((-248012794827/5000000000000 : ℚ) : ℝ) ≤ stT214 393 := by
  have hc : ((-983331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).2
  have h0 : (0:ℝ) ≤ ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248012794827/5000000000000 : ℚ) : ℝ)
      = ((252217/5000000 : ℚ) : ℝ) * ((-983331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c394 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-467821/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6952173/10000000) (δ := 5433/500000000) (ψ := -4983/100000) 214 204
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t394 : ((-117848769939/2500000000000 : ℚ) : ℝ) ≤ stT214 394 := by
  have hc : ((-233923/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).2
  have h0 : (0:ℝ) ≤ ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117848769939/2500000000000 : ℚ) : ℝ)
      = ((503793/10000000 : ℚ) : ℝ) * ((-233923/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c395 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-619123/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1119211/2000000) (δ := 5433/500000000) (ψ := -4983/100000) 214 204
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t395 : ((-62307998163/2000000000000 : ℚ) : ℝ) ≤ stT214 395 := by
  have hc : ((-619173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62307998163/2000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-619173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c396 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-12619/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1060827/2500000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t396 : ((-396487491/62500000000 : ℚ) : ℝ) ≤ stT214 396 := by
  have hc : ((-789/6250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-396487491/62500000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-789/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c397 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((16061/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1447019/5000000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t397 : ((1611954243/80000000000 : ℚ) : ℝ) ≤ stT214 397 := by
  have hc : ((16059/40000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).1
  have hw2 : ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((100377/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1611954243/80000000000 : ℚ) : ℝ)
      = ((100377/2000000 : ℚ) : ℝ) * ((16059/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c398 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((814323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -309617/2000000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t398 : ((204078799171/5000000000000 : ℚ) : ℝ) ≤ stT214 398 := by
  have hc : ((814273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).1
  have hw2 : ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250627/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204078799171/5000000000000 : ℚ) : ℝ)
      = ((250627/5000000 : ℚ) : ℝ) * ((814273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c399 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((498311/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51389/2500000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t399 : ((62363731759/1250000000000 : ℚ) : ℝ) ≤ stT214 399 := by
  have hc : ((249143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62363731759/1250000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((249143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c400 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((179789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1133603/10000000) (δ := 5433/500000000) (ψ := -4983/100000) 214 204
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t400 : ((179779/4000000 : ℚ) : ℝ) ≤ stT214 400 := by
  have hc : ((179779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179779/4000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((179779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c401 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((275273/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 617361/2500000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t401 : ((536922833/19531250000 : ℚ) : ℝ) ≤ stT214 401 := by
  have hc : ((17203/31250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((536922833/19531250000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((17203/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c402 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((50009/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 760383/2000000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t402 : ((12458625543/5000000000000 : ℚ) : ℝ) ≤ stT214 402 := by
  have hc : ((49959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).1
  have hw2 : ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((249377/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12458625543/5000000000000 : ℚ) : ℝ)
      = ((249377/5000000 : ℚ) : ℝ) * ((49959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c403 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-92649/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5131123/10000000) (δ := 5433/500000000) (ψ := -4983/100000) 214 204
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t403 : ((-5769597953/250000000000 : ℚ) : ℝ) ≤ stT214 403 := by
  have hc : ((-92659/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5769597953/250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-92659/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c404 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-847899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6457013/10000000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t404 : ((-421870738531/10000000000000 : ℚ) : ℝ) ≤ stT214 404 := by
  have hc : ((-847949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-421870738531/10000000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-847949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c405 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-499779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194491/250000) (δ := 10737/1000000000) (ψ := -4983/100000) 214 204
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t405 : ((-7761081463/156250000000 : ℚ) : ℝ) ≤ stT214 405 := by
  have hc : ((-124951/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7761081463/156250000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-124951/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c406 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-109817/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20653/31250) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t406 : ((-54504400389/1250000000000 : ℚ) : ℝ) ≤ stT214 406 := by
  have hc : ((-439293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).2
  have h0 : (0:ℝ) ≤ ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54504400389/1250000000000 : ℚ) : ℝ)
      = ((124073/2500000 : ℚ) : ℝ) * ((-439293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c407 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-51957/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264643/500000) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t407 : ((-6439157021/250000000000 : ℚ) : ℝ) ≤ stT214 407 := by
  have hc : ((-25981/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).2
  have h0 : (0:ℝ) ≤ ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6439157021/250000000000 : ℚ) : ℝ)
      = ((247841/5000000 : ℚ) : ℝ) * ((-25981/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c408 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-2119/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -397997/1000000) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t408 : ((-131442147/125000000000 : ℚ) : ℝ) ≤ stT214 408 := by
  have hc : ((-531/25000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).2
  have h0 : (0:ℝ) ≤ ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131442147/125000000000 : ℚ) : ℝ)
      = ((247537/5000000 : ℚ) : ℝ) * ((-531/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c409 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((30111/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267029/1000000) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t409 : ((29774761471/1250000000000 : ℚ) : ℝ) ≤ stT214 409 := by
  have hc : ((240863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29774761471/1250000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((240863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c410 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((854853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68191/500000) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t410 : ((52769553599/1250000000000 : ℚ) : ℝ) ≤ stT214 410 := by
  have hc : ((854803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).1
  have hw2 : ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61733/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52769553599/1250000000000 : ℚ) : ℝ)
      = ((61733/1250000 : ℚ) : ℝ) * ((854803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c411 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((999707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -30253/5000000) (δ := 10773/1000000000) (ψ := -4983/100000) 214 205
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t411 : ((493093810791/10000000000000 : ℚ) : ℝ) ≤ stT214 411 := by
  have hc : ((999657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).1
  have hw2 : ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((493263/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((493093810791/10000000000000 : ℚ) : ℝ)
      = ((493263/10000000 : ℚ) : ℝ) * ((999657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c412 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((87957/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239597/10000000) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t412 : ((338521751/7812500000 : ℚ) : ℝ) ≤ stT214 412 := by
  have hc : ((5497/6250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).1
  have hw2 : ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61583/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((338521751/7812500000 : ℚ) : ℝ)
      = ((61583/1250000 : ℚ) : ℝ) * ((5497/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c413 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((105589/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79267/312500) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t413 : ((51951941793/2000000000000 : ℚ) : ℝ) ≤ stT214 413 := by
  have hc : ((105579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).1
  have hw2 : ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((492067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51951941793/2000000000000 : ℚ) : ℝ)
      = ((492067/10000000 : ℚ) : ℝ) * ((105579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c414 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((4829/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 957597/2500000) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t414 : ((9481005643/5000000000000 : ℚ) : ℝ) ≤ stT214 414 := by
  have hc : ((19291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9481005643/5000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((19291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c415 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-229849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5121129/10000000) (δ := 1083/100000000) (ψ := -4983/100000) 214 205
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t415 : ((-56420389497/2500000000000 : ℚ) : ℝ) ≤ stT214 415 := by
  have hc : ((-114937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).2
  have h0 : (0:ℝ) ≤ ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56420389497/2500000000000 : ℚ) : ℝ)
      = ((490881/10000000 : ℚ) : ℝ) * ((-114937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c416 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-837499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3204357/5000000) (δ := 10773/1000000000) (ψ := -4983/100000) 214 205
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t416 : ((-410642736759/10000000000000 : ℚ) : ℝ) ≤ stT214 416 := by
  have hc : ((-837549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).2
  have h0 : (0:ℝ) ≤ ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-410642736759/10000000000000 : ℚ) : ℝ)
      = ((490291/10000000 : ℚ) : ℝ) * ((-837549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c417 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-498967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7693249/10000000) (δ := 10773/1000000000) (ψ := -4983/100000) 214 205
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t417 : ((-15272367461/312500000000 : ℚ) : ℝ) ≤ stT214 417 := by
  have hc : ((-31187/31250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).2
  have h0 : (0:ℝ) ≤ ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15272367461/312500000000 : ℚ) : ℝ)
      = ((489703/10000000 : ℚ) : ℝ) * ((-31187/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c418 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-450597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3366641/5000000) (δ := 17/1562500) (ψ := -4983/100000) 214 206
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t418 : ((-27550803769/625000000000 : ℚ) : ℝ) ≤ stT214 418 := by
  have hc : ((-225311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27550803769/625000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-225311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c419 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-573821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -54549/100000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t419 : ((-70088586843/2500000000000 : ℚ) : ℝ) ≤ stT214 419 := by
  have hc : ((-573871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70088586843/2500000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-573871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c420 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-100859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4179567/10000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t420 : ((-49238647459/10000000000000 : ℚ) : ℝ) ≤ stT214 420 := by
  have hc : ((-100909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49238647459/10000000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-100909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c421 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((396667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2907283/10000000) (δ := 17/1562500) (ψ := -4983/100000) 214 206
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t421 : ((19329922729/1000000000000 : ℚ) : ℝ) ≤ stT214 421 := by
  have hc : ((396617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).1
  have hw2 : ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((48737/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19329922729/1000000000000 : ℚ) : ℝ)
      = ((48737/1000000 : ℚ) : ℝ) * ((396617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c422 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((792927/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409499/2500000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t422 : ((48245772573/1250000000000 : ℚ) : ℝ) ≤ stT214 422 := by
  have hc : ((792877/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48245772573/1250000000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((792877/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c423 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((247241/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -185879/5000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t423 : ((30051613089/625000000000 : ℚ) : ℝ) ≤ stT214 423 := by
  have hc : ((494457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30051613089/625000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((494457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c424 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((234271/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 445769/5000000) (δ := 17/1562500) (ψ := -4983/100000) 214 206
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t424 : ((113765766457/2500000000000 : ℚ) : ℝ) ≤ stT214 424 := by
  have hc : ((468517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((113765766457/2500000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((468517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c425 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((16297/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2151837/10000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t425 : ((31618382993/1000000000000 : ℚ) : ℝ) ≤ stT214 425 := by
  have hc : ((65183/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31618382993/1000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((65183/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c426 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((205641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1704597/5000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t426 : ((99609045091/10000000000000 : ℚ) : ℝ) ≤ stT214 426 := by
  have hc : ((205591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99609045091/10000000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((205591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c427 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-145201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4663609/10000000) (δ := 17/1562500) (ψ := -4983/100000) 214 206
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t427 : ((-17569949771/1250000000000 : ℚ) : ℝ) ≤ stT214 427 := by
  have hc : ((-72613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17569949771/1250000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-72613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c428 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-357007/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5915027/10000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t428 : ((-21572275101/625000000000 : ℚ) : ℝ) ≤ stT214 428 := by
  have hc : ((-44629/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21572275101/625000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-44629/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c429 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-962113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 716361/1000000) (δ := 10723/1000000000) (ψ := -4983/100000) 214 206
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t429 : ((-92907421443/2000000000000 : ℚ) : ℝ) ≤ stT214 429 := by
  have hc : ((-962163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92907421443/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-962163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c430 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-195087/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7298713/10000000) (δ := 2163/200000000) (ψ := -4983/100000) 214 207
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t430 : ((-94084162571/2000000000000 : ℚ) : ℝ) ≤ stT214 430 := by
  have hc : ((-195097/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94084162571/2000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-195097/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c431 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-376171/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1211203/2000000) (δ := 2163/200000000) (ψ := -4983/100000) 214 207
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t431 : ((-11325474629/312500000000 : ℚ) : ℝ) ≤ stT214 431 := by
  have hc : ((-94049/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).2
  have h0 : (0:ℝ) ≤ ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11325474629/312500000000 : ℚ) : ℝ)
      = ((120421/2500000 : ℚ) : ℝ) * ((-94049/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c432 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-348213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -602019/1250000) (δ := 2697/250000000) (ψ := -4983/100000) 214 207
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t432 : ((-83779192069/5000000000000 : ℚ) : ℝ) ≤ stT214 432 := by
  have hc : ((-348263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).2
  have h0 : (0:ℝ) ≤ ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-83779192069/5000000000000 : ℚ) : ℝ)
      = ((240563/5000000 : ℚ) : ℝ) * ((-348263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c433 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((69349/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28633/80000) (δ := 2697/250000000) (ψ := -4983/100000) 214 207
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t433 : ((8328741339/1250000000000 : ℚ) : ℝ) ≤ stT214 433 := by
  have hc : ((17331/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8328741339/1250000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((17331/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c434 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((295703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2344987/10000000) (δ := 2697/250000000) (ψ := -4983/100000) 214 207
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t434 : ((14192987517/500000000000 : ℚ) : ℝ) ≤ stT214 434 := by
  have hc : ((147839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14192987517/500000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((147839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c435 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((902407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222737/2000000) (δ := 2163/200000000) (ψ := -4983/100000) 214 207
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t435 : ((432646794291/10000000000000 : ℚ) : ℝ) ≤ stT214 435 := by
  have hc : ((902357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).1
  have hw2 : ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((479463/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432646794291/10000000000000 : ℚ) : ℝ)
      = ((479463/10000000 : ℚ) : ℝ) * ((902357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c436 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((499473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 57391/5000000) (δ := 2163/200000000) (ψ := -4983/100000) 214 207
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t436 : ((29899017503/625000000000 : ℚ) : ℝ) ≤ stT214 436 := by
  have hc : ((62431/62500 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).1
  have hw2 : ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29899017503/625000000000 : ℚ) : ℝ)
      = ((478913/10000000 : ℚ) : ℝ) * ((62431/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c437 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((429837/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 670207/5000000) (δ := 2697/250000000) (ψ := -4983/100000) 214 207
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t437 : ((12850411723/312500000000 : ℚ) : ℝ) ≤ stT214 437 := by
  have hc : ((107453/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).1
  have hw2 : ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((119591/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12850411723/312500000000 : ℚ) : ℝ)
      = ((119591/2500000 : ℚ) : ℝ) * ((107453/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c438 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((25941/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2563317/10000000) (δ := 2697/250000000) (ψ := -4983/100000) 214 207
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t438 : ((12393882193/500000000000 : ℚ) : ℝ) ≤ stT214 438 := by
  have hc : ((51877/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).1
  have hw2 : ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((238909/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12393882193/500000000000 : ℚ) : ℝ)
      = ((238909/5000000 : ℚ) : ℝ) * ((51877/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c439 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((57411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 472923/1250000) (δ := 2163/200000000) (ψ := -4983/100000) 214 207
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t439 : ((27376856553/10000000000000 : ℚ) : ℝ) ≤ stT214 439 := by
  have hc : ((57361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27376856553/10000000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((57361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c440 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-416391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 500067/1000000) (δ := 2697/250000000) (ψ := -4983/100000) 214 207
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t440 : ((-49632687703/2500000000000 : ℚ) : ℝ) ≤ stT214 440 := by
  have hc : ((-416441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).2
  have h0 : (0:ℝ) ≤ ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49632687703/2500000000000 : ℚ) : ℝ)
      = ((119183/2500000 : ℚ) : ℝ) * ((-416441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c441 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-792729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6215173/10000000) (δ := 2163/200000000) (ψ := -4983/100000) 214 207
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t441 : ((-377514224789/10000000000000 : ℚ) : ℝ) ≤ stT214 441 := by
  have hc : ((-792779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).2
  have h0 : (0:ℝ) ≤ ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-377514224789/10000000000000 : ℚ) : ℝ)
      = ((476191/10000000 : ℚ) : ℝ) * ((-792779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c442 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-985447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1856737/2500000) (δ := 2163/200000000) (ψ := -4983/100000) 214 207
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t442 : ((-117188404761/2500000000000 : ℚ) : ℝ) ≤ stT214 442 := by
  have hc : ((-985497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).2
  have h0 : (0:ℝ) ≤ ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117188404761/2500000000000 : ℚ) : ℝ)
      = ((118913/2500000 : ℚ) : ℝ) * ((-985497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c443 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-475737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220999/312500) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t443 : ((-22604166263/500000000000 : ℚ) : ℝ) ≤ stT214 443 := by
  have hc : ((-237881/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22604166263/500000000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-237881/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c444 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-700047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -117313/200000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t444 : ((-332251334163/10000000000000 : ℚ) : ℝ) ≤ stT214 444 := by
  have hc : ((-700097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-332251334163/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-700097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c445 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-28981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4662061/10000000) (δ := 2677/250000000) (ψ := -4983/100000) 214 208
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t445 : ((-3435174339/250000000000 : ℚ) : ℝ) ≤ stT214 445 := by
  have hc : ((-14493/50000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3435174339/250000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-14493/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c446 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((185261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1730573/5000000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t446 : ((87699816243/10000000000000 : ℚ) : ℝ) ≤ stT214 446 := by
  have hc : ((185211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).1
  have hw2 : ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((473513/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87699816243/10000000000000 : ℚ) : ℝ)
      = ((473513/10000000 : ℚ) : ℝ) * ((185211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c447 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((617541/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28287/125000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t447 : ((292062745653/10000000000000 : ℚ) : ℝ) ≤ stT214 447 := by
  have hc : ((617491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).1
  have hw2 : ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((472983/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292062745653/10000000000000 : ℚ) : ℝ)
      = ((472983/10000000 : ℚ) : ℝ) * ((617491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c448 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((910229/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -266849/2500000) (δ := 2677/250000000) (ψ := -4983/100000) 214 208
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t448 : ((86003723889/2000000000000 : ℚ) : ℝ) ≤ stT214 448 := by
  have hc : ((910179/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86003723889/2000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((910179/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c449 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((998741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196/15625) (δ := 2677/250000000) (ψ := -4983/100000) 214 208
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t449 : ((471311244939/10000000000000 : ℚ) : ℝ) ≤ stT214 449 := by
  have hc : ((998691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((471311244939/10000000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((998691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c450 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((864691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 263131/2000000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t450 : ((101898806491/2500000000000 : ℚ) : ℝ) ≤ stT214 450 := by
  have hc : ((864641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101898806491/2500000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((864641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c451 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((539209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156453/625000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t451 : ((253879729079/10000000000000 : ℚ) : ℝ) ≤ stT214 451 := by
  have hc : ((539159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253879729079/10000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((539159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c452 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((19077/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1844083/5000000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t452 : ((224208853/50000000000 : ℚ) : ℝ) ≤ stT214 452 := by
  have hc : ((19067/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).1
  have hw2 : ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224208853/50000000000 : ℚ) : ℝ)
      = ((11759/250000 : ℚ) : ℝ) * ((19067/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c453 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-184257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1217629/2500000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t453 : ((-43291619581/2500000000000 : ℚ) : ℝ) ≤ stT214 453 := by
  have hc : ((-92141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43291619581/2500000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-92141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c454 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-150161/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6050191/10000000) (δ := 2179/200000000) (ψ := -4983/100000) 214 208
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t454 : ((-17619713601/500000000000 : ℚ) : ℝ) ≤ stT214 454 := by
  have hc : ((-150171/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17619713601/500000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-150171/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c455 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-968751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7227351/10000000) (δ := 2677/250000000) (ψ := -4983/100000) 214 208
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t455 : ((-56772707401/1250000000000 : ℚ) : ℝ) ≤ stT214 455 := by
  have hc : ((-968801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56772707401/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-968801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c456 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-12201/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7306073/10000000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t456 : ((-45711484609/1000000000000 : ℚ) : ℝ) ≤ stT214 456 := by
  have hc : ((-97613/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45711484609/1000000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-97613/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c457 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-386281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533539/2500000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 209
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t457 : ((-90353303493/2500000000000 : ℚ) : ℝ) ≤ stT214 457 := by
  have hc : ((-193153/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).2
  have h0 : (0:ℝ) ≤ ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90353303493/2500000000000 : ℚ) : ℝ)
      = ((467781/10000000 : ℚ) : ℝ) * ((-193153/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c458 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-201643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4964753/10000000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 209
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t458 : ((-2355835159/125000000000 : ℚ) : ℝ) ≤ stT214 458 := by
  have hc : ((-50417/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).2
  have h0 : (0:ℝ) ≤ ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2355835159/125000000000 : ℚ) : ℝ)
      = ((46727/1000000 : ℚ) : ℝ) * ((-50417/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c459 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((12907/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -474733/1250000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t459 : ((300931841/125000000000 : ℚ) : ℝ) ≤ stT214 459 := by
  have hc : ((25789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300931841/125000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((25789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c460 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((98917/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2633597/10000000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t460 : ((11528896641/500000000000 : ℚ) : ℝ) ≤ stT214 460 := by
  have hc : ((98907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11528896641/500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((98907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c461 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((415827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1471791/10000000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t461 : ((48414529573/1250000000000 : ℚ) : ℝ) ≤ stT214 461 := by
  have hc : ((207901/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).1
  have hw2 : ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232873/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48414529573/1250000000000 : ℚ) : ℝ)
      = ((232873/5000000 : ℚ) : ℝ) * ((207901/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c462 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((198439/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -312553/10000000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t462 : ((46158752409/1000000000000 : ℚ) : ℝ) ≤ stT214 462 := by
  have hc : ((198429/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).1
  have hw2 : ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232621/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46158752409/1000000000000 : ℚ) : ℝ)
      = ((232621/5000000 : ℚ) : ℝ) * ((198429/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c463 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((943523/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13191/156250) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t463 : ((438468698547/10000000000000 : ℚ) : ℝ) ≤ stT214 463 := by
  have hc : ((943473/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).1
  have hw2 : ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((464739/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((438468698547/10000000000000 : ℚ) : ℝ)
      = ((464739/10000000 : ℚ) : ℝ) * ((943473/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c464 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((697141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 999243/5000000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 209
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t464 : ((161808065829/5000000000000 : ℚ) : ℝ) ≤ stT214 464 := by
  have hc : ((697091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).1
  have hw2 : ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161808065829/5000000000000 : ℚ) : ℝ)
      = ((232119/5000000 : ℚ) : ℝ) * ((697091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c465 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((305707/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196893/625000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t465 : ((70872382933/5000000000000 : ℚ) : ℝ) ≤ stT214 465 := by
  have hc : ((305657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).1
  have hw2 : ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((231869/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70872382933/5000000000000 : ℚ) : ℝ)
      = ((231869/5000000 : ℚ) : ℝ) * ((305657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c466 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-148483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171983/400000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t466 : ((-34403361993/5000000000000 : ℚ) : ℝ) ≤ stT214 466 := by
  have hc : ((-148533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).2
  have h0 : (0:ℝ) ≤ ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34403361993/5000000000000 : ℚ) : ℝ)
      = ((231621/5000000 : ℚ) : ℝ) * ((-148533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c467 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-571033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5446401/10000000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t467 : ((-52853160567/2000000000000 : ℚ) : ℝ) ≤ stT214 467 := by
  have hc : ((-571083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).2
  have h0 : (0:ℝ) ≤ ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-52853160567/2000000000000 : ℚ) : ℝ)
      = ((92549/2000000 : ℚ) : ℝ) * ((-571083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c468 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-218759/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3295383/5000000) (δ := 5401/500000000) (ψ := -4983/100000) 214 209
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t468 : ((-202254689293/5000000000000 : ℚ) : ℝ) ≤ stT214 468 := by
  have hc : ((-437543/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).2
  have h0 : (0:ℝ) ≤ ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202254689293/5000000000000 : ℚ) : ℝ)
      = ((462251/10000000 : ℚ) : ℝ) * ((-437543/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c469 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-124853/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7732723/10000000) (δ := 10801/1000000000) (ψ := -4983/100000) 214 209
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t469 : ((-115309515123/2500000000000 : ℚ) : ℝ) ≤ stT214 469 := by
  have hc : ((-499437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).2
  have h0 : (0:ℝ) ≤ ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115309515123/2500000000000 : ℚ) : ℝ)
      = ((230879/5000000 : ℚ) : ℝ) * ((-499437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c470 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-229549/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -213617/312500) (δ := 5447/500000000) (ψ := -4983/100000) 214 210
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t470 : ((-105888914859/2500000000000 : ℚ) : ℝ) ≤ stT214 470 := by
  have hc : ((-459123/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105888914859/2500000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-459123/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c471 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-650821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1139731/2000000) (δ := 5447/500000000) (ψ := -4983/100000) 214 210
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t471 : ((-37488216987/1250000000000 : ℚ) : ℝ) ≤ stT214 471 := by
  have hc : ((-650871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37488216987/1250000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-650871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c472 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-50409/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4563973/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 210
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t472 : ((-45326681/3906250000 : ℚ) : ℝ) ≤ stT214 472 := by
  have hc : ((-50419/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45326681/3906250000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-50419/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c473 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((196823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3431699/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 210
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t473 : ((452381127/50000000000 : ℚ) : ℝ) ≤ stT214 473 := by
  have hc : ((196773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).1
  have hw2 : ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2299/50000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452381127/50000000000 : ℚ) : ℝ)
      = ((2299/50000 : ℚ) : ℝ) * ((196773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c474 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((302627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2301779/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 210
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t474 : ((13898963763/500000000000 : ℚ) : ℝ) ≤ stT214 474 := by
  have hc : ((151301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).1
  have hw2 : ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13898963763/500000000000 : ℚ) : ℝ)
      = ((91863/2000000 : ℚ) : ℝ) * ((151301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c475 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((891701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1174267/10000000) (δ := 5447/500000000) (ψ := -4983/100000) 214 210
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t475 : ((409117119981/10000000000000 : ℚ) : ℝ) ≤ stT214 475 := by
  have hc : ((891651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409117119981/10000000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((891651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c476 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((999807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -24581/5000000) (δ := 5447/500000000) (ψ := -4983/100000) 214 210
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t476 : ((458237621193/10000000000000 : ℚ) : ℝ) ≤ stT214 476 := by
  have hc : ((999757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458237621193/10000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((999757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c477 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((909201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1073589/10000000) (δ := 5447/500000000) (ψ := -4983/100000) 214 210
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t477 : ((104067787517/2500000000000 : ℚ) : ℝ) ≤ stT214 477 := by
  have hc : ((909151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104067787517/2500000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((909151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c478 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((638987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 54851/250000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 210
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t478 : ((292242755493/10000000000000 : ℚ) : ℝ) ≤ stT214 478 := by
  have hc : ((638937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292242755493/10000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((638937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c479 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((243491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3312083/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 210
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t479 : ((111230870751/10000000000000 : ℚ) : ℝ) ≤ stT214 479 := by
  have hc : ((243441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).1
  have hw2 : ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((456911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111230870751/10000000000000 : ℚ) : ℝ)
      = ((456911/10000000 : ℚ) : ℝ) * ((243441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c480 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-99509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4427879/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 210
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t480 : ((-5678862603/625000000000 : ℚ) : ℝ) ≤ stT214 480 := by
  have hc : ((-49767/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5678862603/625000000000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-49767/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c481 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-300883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5541267/10000000) (δ := 5447/500000000) (ψ := -4983/100000) 214 210
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t481 : ((-34300578147/1250000000000 : ℚ) : ℝ) ≤ stT214 481 := by
  have hc : ((-75227/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34300578147/1250000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-75227/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c482 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-55419/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6652409/10000000) (δ := 10709/1000000000) (ψ := -4983/100000) 214 210
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t482 : ((-3155514109/78125000000 : ℚ) : ℝ) ≤ stT214 482 := by
  have hc : ((-443377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3155514109/78125000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-443377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c483 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-999311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1940299/2500000) (δ := 5447/500000000) (ψ := -4983/100000) 214 210
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t483 : ((-56840655597/1250000000000 : ℚ) : ℝ) ≤ stT214 483 := by
  have hc : ((-999361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56840655597/1250000000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-999361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c484 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-114863/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3420113/5000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t484 : ((-104426716221/2500000000000 : ℚ) : ℝ) ≤ stT214 484 := by
  have hc : ((-459477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).2
  have h0 : (0:ℝ) ≤ ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104426716221/2500000000000 : ℚ) : ℝ)
      = ((227273/5000000 : ℚ) : ℝ) * ((-459477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c485 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-331051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -143401/250000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 211
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t485 : ((-37583499213/1250000000000 : ℚ) : ℝ) ≤ stT214 485 := by
  have hc : ((-82769/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).2
  have h0 : (0:ℝ) ≤ ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37583499213/1250000000000 : ℚ) : ℝ)
      = ((454077/10000000 : ℚ) : ℝ) * ((-82769/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c486 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-279067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4634047/10000000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 211
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t486 : ((-12661026237/1000000000000 : ℚ) : ℝ) ≤ stT214 486 := by
  have hc : ((-279117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).2
  have h0 : (0:ℝ) ≤ ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12661026237/1000000000000 : ℚ) : ℝ)
      = ((45361/1000000 : ℚ) : ℝ) * ((-279117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c487 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((15641/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1767177/5000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t487 : ((1771335987/250000000000 : ℚ) : ℝ) ≤ stT214 487 := by
  have hc : ((3909/25000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1771335987/250000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((3909/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c488 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((140341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2436909/10000000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 211
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t488 : ((63523624723/2500000000000 : ℚ) : ℝ) ≤ stT214 488 := by
  have hc : ((280657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63523624723/2500000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((280657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c489 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((429699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -335441/2500000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 211
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t489 : ((19430502791/500000000000 : ℚ) : ℝ) ≤ stT214 489 := by
  have hc : ((214837/250000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).1
  have hw2 : ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90443/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19430502791/500000000000 : ℚ) : ℝ)
      = ((90443/2000000 : ℚ) : ℝ) * ((214837/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c490 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((995051/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62203/2500000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t490 : ((449494686753/10000000000000 : ℚ) : ℝ) ≤ stT214 490 := by
  have hc : ((995001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).1
  have hw2 : ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451753/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449494686753/10000000000000 : ℚ) : ℝ)
      = ((451753/10000000 : ℚ) : ℝ) * ((995001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c491 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((58989/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420973/5000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t491 : ((212959299891/5000000000000 : ℚ) : ℝ) ≤ stT214 491 := by
  have hc : ((471887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).1
  have hw2 : ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((451293/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212959299891/5000000000000 : ℚ) : ℝ)
      = ((451293/10000000 : ℚ) : ℝ) * ((471887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c492 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((716389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1930457/10000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t492 : ((161474988363/5000000000000 : ℚ) : ℝ) ≤ stT214 492 := by
  have hc : ((716339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).1
  have hw2 : ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((225417/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161474988363/5000000000000 : ℚ) : ℝ)
      = ((225417/5000000 : ℚ) : ℝ) * ((716339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c493 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((89029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3016721/10000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t493 : ((80181968441/5000000000000 : ℚ) : ℝ) ≤ stT214 493 := by
  have hc : ((178033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).1
  have hw2 : ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((450377/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80181968441/5000000000000 : ℚ) : ℝ)
      = ((450377/10000000 : ℚ) : ℝ) * ((178033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c494 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-34743/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 820169/2000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t494 : ((-488840253/156250000000 : ℚ) : ℝ) ≤ stT214 494 := by
  have hc : ((-2173/31250 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).2
  have h0 : (0:ℝ) ≤ ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-488840253/156250000000 : ℚ) : ℝ)
      = ((224961/5000000 : ℚ) : ℝ) * ((-2173/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c495 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-120359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2591361/5000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t495 : ((-108206033981/5000000000000 : ℚ) : ℝ) ≤ stT214 495 := by
  have hc : ((-240743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).2
  have h0 : (0:ℝ) ≤ ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108206033981/5000000000000 : ℚ) : ℝ)
      = ((449467/10000000 : ℚ) : ℝ) * ((-240743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c496 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-201029/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6262459/10000000) (δ := 169/15625000) (ψ := -4983/100000) 214 211
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t496 : ((-90270448081/2500000000000 : ℚ) : ℝ) ≤ stT214 496 := by
  have hc : ((-402083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).2
  have h0 : (0:ℝ) ≤ ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90270448081/2500000000000 : ℚ) : ℝ)
      = ((224507/5000000 : ℚ) : ℝ) * ((-402083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c497 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-48947/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3670001/5000000) (δ := 10787/1000000000) (ψ := -4983/100000) 214 211
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t497 : ((-21956885619/500000000000 : ℚ) : ℝ) ≤ stT214 497 := by
  have hc : ((-97899/100000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).2
  have h0 : (0:ℝ) ≤ ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21956885619/500000000000 : ℚ) : ℝ)
      = ((224281/5000000 : ℚ) : ℝ) * ((-97899/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c498 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-194979/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7292611/10000000) (δ := 2681/250000000) (ψ := -4983/100000) 214 212
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t498 : ((-87376715779/2000000000000 : ℚ) : ℝ) ≤ stT214 498 := by
  have hc : ((-194989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87376715779/2000000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-194989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c499 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-793759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6219401/10000000) (δ := 2681/250000000) (ψ := -4983/100000) 214 212
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t499 : ((-177679062279/5000000000000 : ℚ) : ℝ) ≤ stT214 499 := by
  have hc : ((-793809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177679062279/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-793809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_c500 :
    |Real.cos (((214 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-234667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5148331/10000000) (δ := 2681/250000000) (ψ := -4983/100000) 214 212
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st214_t500 : ((-13119693511/625000000000 : ℚ) : ℝ) ≤ stT214 500 := by
  have hc : ((-58673/125000 : ℚ) : ℝ)
      ≤ Real.cos (((214 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st214_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13119693511/625000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-58673/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st214_p1 : ((998709/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT214 (i+1) := by
  rw [Finset.sum_range_one]
  exact st214_t1

theorem st214_p2 : ((1177581679551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT214 (i+1))
      = (∑ i ∈ Finset.range 1, stT214 (i+1)) + stT214 2 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 1
    simpa using h
  have hprev := st214_p1
  have hstep := st214_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p3 : ((-223150290129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT214 (i+1))
      = (∑ i ∈ Finset.range 2, stT214 (i+1)) + stT214 3 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 2
    simpa using h
  have hprev := st214_p2
  have hstep := st214_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p4 : ((184112209871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT214 (i+1))
      = (∑ i ∈ Finset.range 3, stT214 (i+1)) + stT214 4 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 3
    simpa using h
  have hprev := st214_p3
  have hstep := st214_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p5 : ((1187015316431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT214 (i+1))
      = (∑ i ∈ Finset.range 4, stT214 (i+1)) + stT214 5 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 4
    simpa using h
  have hprev := st214_p4
  have hstep := st214_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p6 : ((3182434538463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT214 (i+1))
      = (∑ i ∈ Finset.range 5, stT214 (i+1)) + stT214 6 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 5
    simpa using h
  have hprev := st214_p5
  have hstep := st214_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p7 : ((347722603691/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT214 (i+1))
      = (∑ i ∈ Finset.range 6, stT214 (i+1)) + stT214 7 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 6
    simpa using h
  have hprev := st214_p6
  have hstep := st214_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p8 : ((7304638420439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT214 (i+1))
      = (∑ i ∈ Finset.range 7, stT214 (i+1)) + stT214 8 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 7
    simpa using h
  have hprev := st214_p7
  have hstep := st214_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p9 : ((183057231379/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT214 (i+1))
      = (∑ i ∈ Finset.range 8, stT214 (i+1)) + stT214 9 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 8
    simpa using h
  have hprev := st214_p8
  have hstep := st214_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p10 : ((3137189522891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT214 (i+1))
      = (∑ i ∈ Finset.range 9, stT214 (i+1)) + stT214 10 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 9
    simpa using h
  have hprev := st214_p9
  have hstep := st214_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p11 : ((31000511299/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT214 (i+1))
      = (∑ i ∈ Finset.range 10, stT214 (i+1)) + stT214 11 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 10
    simpa using h
  have hprev := st214_p10
  have hstep := st214_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p12 : ((98266873953/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT214 (i+1))
      = (∑ i ∈ Finset.range 11, stT214 (i+1)) + stT214 12 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 11
    simpa using h
  have hprev := st214_p11
  have hstep := st214_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p13 : ((636033118183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT214 (i+1))
      = (∑ i ∈ Finset.range 12, stT214 (i+1)) + stT214 13 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 12
    simpa using h
  have hprev := st214_p12
  have hstep := st214_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p14 : ((1676237762091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT214 (i+1))
      = (∑ i ∈ Finset.range 13, stT214 (i+1)) + stT214 14 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 13
    simpa using h
  have hprev := st214_p13
  have hstep := st214_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p15 : ((1742322453957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT214 (i+1))
      = (∑ i ∈ Finset.range 14, stT214 (i+1)) + stT214 15 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 14
    simpa using h
  have hprev := st214_p14
  have hstep := st214_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p16 : ((14503237227/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT214 (i+1))
      = (∑ i ∈ Finset.range 15, stT214 (i+1)) + stT214 16 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 15
    simpa using h
  have hprev := st214_p15
  have hstep := st214_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p17 : ((-1264120602969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT214 (i+1))
      = (∑ i ∈ Finset.range 16, stT214 (i+1)) + stT214 17 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 16
    simpa using h
  have hprev := st214_p16
  have hstep := st214_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p18 : ((-3512923248947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT214 (i+1))
      = (∑ i ∈ Finset.range 17, stT214 (i+1)) + stT214 18 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 17
    simpa using h
  have hprev := st214_p17
  have hstep := st214_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p19 : ((-4125931443179/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT214 (i+1))
      = (∑ i ∈ Finset.range 18, stT214 (i+1)) + stT214 19 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 18
    simpa using h
  have hprev := st214_p18
  have hstep := st214_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p20 : ((-1960394468493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT214 (i+1))
      = (∑ i ∈ Finset.range 19, stT214 (i+1)) + stT214 20 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 19
    simpa using h
  have hprev := st214_p19
  have hstep := st214_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p21 : ((-52226027343/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT214 (i+1))
      = (∑ i ∈ Finset.range 20, stT214 (i+1)) + stT214 21 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 20
    simpa using h
  have hprev := st214_p20
  have hstep := st214_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p22 : ((-1546300020571/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT214 (i+1))
      = (∑ i ∈ Finset.range 21, stT214 (i+1)) + stT214 22 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 21
    simpa using h
  have hprev := st214_p21
  have hstep := st214_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p23 : ((-1222783673539/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT214 (i+1))
      = (∑ i ∈ Finset.range 22, stT214 (i+1)) + stT214 23 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 22
    simpa using h
  have hprev := st214_p22
  have hstep := st214_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p24 : ((-305337170279/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT214 (i+1))
      = (∑ i ∈ Finset.range 23, stT214 (i+1)) + stT214 24 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 23
    simpa using h
  have hprev := st214_p23
  have hstep := st214_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p25 : ((-371637399907/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT214 (i+1))
      = (∑ i ∈ Finset.range 24, stT214 (i+1)) + stT214 25 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 24
    simpa using h
  have hprev := st214_p24
  have hstep := st214_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p26 : ((-177764868091/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT214 (i+1))
      = (∑ i ∈ Finset.range 25, stT214 (i+1)) + stT214 26 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 25
    simpa using h
  have hprev := st214_p25
  have hstep := st214_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p27 : ((-382994289953/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT214 (i+1))
      = (∑ i ∈ Finset.range 26, stT214 (i+1)) + stT214 27 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 26
    simpa using h
  have hprev := st214_p26
  have hstep := st214_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p28 : ((-760977788183/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT214 (i+1))
      = (∑ i ∈ Finset.range 27, stT214 (i+1)) + stT214 28 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 27
    simpa using h
  have hprev := st214_p27
  have hstep := st214_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p29 : ((-4431900600739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT214 (i+1))
      = (∑ i ∈ Finset.range 28, stT214 (i+1)) + stT214 29 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 28
    simpa using h
  have hprev := st214_p28
  have hstep := st214_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p30 : ((-3360260011897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT214 (i+1))
      = (∑ i ∈ Finset.range 29, stT214 (i+1)) + stT214 30 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 29
    simpa using h
  have hprev := st214_p29
  have hstep := st214_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p31 : ((-1603598046293/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT214 (i+1))
      = (∑ i ∈ Finset.range 30, stT214 (i+1)) + stT214 31 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 30
    simpa using h
  have hprev := st214_p30
  have hstep := st214_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p32 : ((84362157637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT214 (i+1))
      = (∑ i ∈ Finset.range 31, stT214 (i+1)) + stT214 32 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 31
    simpa using h
  have hprev := st214_p31
  have hstep := st214_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p33 : ((1517654448101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT214 (i+1))
      = (∑ i ∈ Finset.range 32, stT214 (i+1)) + stT214 33 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 32
    simpa using h
  have hprev := st214_p32
  have hstep := st214_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p34 : ((2819544151211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT214 (i+1))
      = (∑ i ∈ Finset.range 33, stT214 (i+1)) + stT214 34 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 33
    simpa using h
  have hprev := st214_p33
  have hstep := st214_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p35 : ((4186379599559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT214 (i+1))
      = (∑ i ∈ Finset.range 34, stT214 (i+1)) + stT214 35 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 34
    simpa using h
  have hprev := st214_p34
  have hstep := st214_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p36 : ((5737582312411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT214 (i+1))
      = (∑ i ∈ Finset.range 35, stT214 (i+1)) + stT214 36 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 35
    simpa using h
  have hprev := st214_p35
  have hstep := st214_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p37 : ((7379785940357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT214 (i+1))
      = (∑ i ∈ Finset.range 36, stT214 (i+1)) + stT214 37 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 36
    simpa using h
  have hprev := st214_p36
  have hstep := st214_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p38 : ((8698375012619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT214 (i+1))
      = (∑ i ∈ Finset.range 37, stT214 (i+1)) + stT214 38 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 37
    simpa using h
  have hprev := st214_p37
  have hstep := st214_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p39 : ((452750695911/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT214 (i+1))
      = (∑ i ∈ Finset.range 38, stT214 (i+1)) + stT214 39 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 38
    simpa using h
  have hprev := st214_p38
  have hstep := st214_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p40 : ((8110025640063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT214 (i+1))
      = (∑ i ∈ Finset.range 39, stT214 (i+1)) + stT214 40 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 39
    simpa using h
  have hprev := st214_p39
  have hstep := st214_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p41 : ((6551892131367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT214 (i+1))
      = (∑ i ∈ Finset.range 40, stT214 (i+1)) + stT214 41 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 40
    simpa using h
  have hprev := st214_p40
  have hstep := st214_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p42 : ((5985489097953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT214 (i+1))
      = (∑ i ∈ Finset.range 41, stT214 (i+1)) + stT214 42 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 41
    simpa using h
  have hprev := st214_p41
  have hstep := st214_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p43 : ((3576411970429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT214 (i+1))
      = (∑ i ∈ Finset.range 42, stT214 (i+1)) + stT214 43 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 42
    simpa using h
  have hprev := st214_p42
  have hstep := st214_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p44 : ((166790897761/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT214 (i+1))
      = (∑ i ∈ Finset.range 43, stT214 (i+1)) + stT214 44 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 43
    simpa using h
  have hprev := st214_p43
  have hstep := st214_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p45 : ((3768961727161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT214 (i+1))
      = (∑ i ∈ Finset.range 44, stT214 (i+1)) + stT214 45 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 44
    simpa using h
  have hprev := st214_p44
  have hstep := st214_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p46 : ((3150907716671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT214 (i+1))
      = (∑ i ∈ Finset.range 45, stT214 (i+1)) + stT214 46 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 45
    simpa using h
  have hprev := st214_p45
  have hstep := st214_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p47 : ((3613223599923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT214 (i+1))
      = (∑ i ∈ Finset.range 46, stT214 (i+1)) + stT214 47 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 46
    simpa using h
  have hprev := st214_p46
  have hstep := st214_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p48 : ((4065401233173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT214 (i+1))
      = (∑ i ∈ Finset.range 47, stT214 (i+1)) + stT214 48 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 47
    simpa using h
  have hprev := st214_p47
  have hstep := st214_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p49 : ((3401323110399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT214 (i+1))
      = (∑ i ∈ Finset.range 48, stT214 (i+1)) + stT214 49 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 48
    simpa using h
  have hprev := st214_p48
  have hstep := st214_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p50 : ((272763684151/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT214 (i+1))
      = (∑ i ∈ Finset.range 49, stT214 (i+1)) + stT214 50 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 49
    simpa using h
  have hprev := st214_p49
  have hstep := st214_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p51 : ((1611391565483/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT214 (i+1))
      = (∑ i ∈ Finset.range 50, stT214 (i+1)) + stT214 51 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 50
    simpa using h
  have hprev := st214_p50
  have hstep := st214_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p52 : ((6858688476331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT214 (i+1))
      = (∑ i ∈ Finset.range 51, stT214 (i+1)) + stT214 52 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 51
    simpa using h
  have hprev := st214_p51
  have hstep := st214_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p53 : ((3503685801173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT214 (i+1))
      = (∑ i ∈ Finset.range 52, stT214 (i+1)) + stT214 53 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 52
    simpa using h
  have hprev := st214_p52
  have hstep := st214_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p54 : ((1586981440613/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT214 (i+1))
      = (∑ i ∈ Finset.range 53, stT214 (i+1)) + stT214 54 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 53
    simpa using h
  have hprev := st214_p53
  have hstep := st214_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p55 : ((1317459473093/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT214 (i+1))
      = (∑ i ∈ Finset.range 54, stT214 (i+1)) + stT214 55 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 54
    simpa using h
  have hprev := st214_p54
  have hstep := st214_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p56 : ((7627400450117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT214 (i+1))
      = (∑ i ∈ Finset.range 55, stT214 (i+1)) + stT214 56 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 55
    simpa using h
  have hprev := st214_p55
  have hstep := st214_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p57 : ((3652401907651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT214 (i+1))
      = (∑ i ∈ Finset.range 56, stT214 (i+1)) + stT214 57 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 56
    simpa using h
  have hprev := st214_p56
  have hstep := st214_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p58 : ((429621409037/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT214 (i+1))
      = (∑ i ∈ Finset.range 57, stT214 (i+1)) + stT214 58 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 57
    simpa using h
  have hprev := st214_p57
  have hstep := st214_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p59 : ((7852719619349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT214 (i+1))
      = (∑ i ∈ Finset.range 58, stT214 (i+1)) + stT214 59 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 58
    simpa using h
  have hprev := st214_p58
  have hstep := st214_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p60 : ((6606653827339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT214 (i+1))
      = (∑ i ∈ Finset.range 59, stT214 (i+1)) + stT214 60 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 59
    simpa using h
  have hprev := st214_p59
  have hstep := st214_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p61 : ((7876005541067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT214 (i+1))
      = (∑ i ∈ Finset.range 60, stT214 (i+1)) + stT214 61 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 60
    simpa using h
  have hprev := st214_p60
  have hstep := st214_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p62 : ((6743100256967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT214 (i+1))
      = (∑ i ∈ Finset.range 61, stT214 (i+1)) + stT214 62 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 61
    simpa using h
  have hprev := st214_p61
  have hstep := st214_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p63 : ((7663556716757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT214 (i+1))
      = (∑ i ∈ Finset.range 62, stT214 (i+1)) + stT214 63 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 62
    simpa using h
  have hprev := st214_p62
  have hstep := st214_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p64 : ((870912488719/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT214 (i+1))
      = (∑ i ∈ Finset.range 63, stT214 (i+1)) + stT214 64 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 63
    simpa using h
  have hprev := st214_p63
  have hstep := st214_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p65 : ((3733330565629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT214 (i+1))
      = (∑ i ∈ Finset.range 64, stT214 (i+1)) + stT214 65 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 64
    simpa using h
  have hprev := st214_p64
  have hstep := st214_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p66 : ((1779021057527/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT214 (i+1))
      = (∑ i ∈ Finset.range 65, stT214 (i+1)) + stT214 66 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 65
    simpa using h
  have hprev := st214_p65
  have hstep := st214_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p67 : ((3686685882407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT214 (i+1))
      = (∑ i ∈ Finset.range 66, stT214 (i+1)) + stT214 67 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 66
    simpa using h
  have hprev := st214_p66
  have hstep := st214_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p68 : ((7152151223597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT214 (i+1))
      = (∑ i ∈ Finset.range 67, stT214 (i+1)) + stT214 68 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 67
    simpa using h
  have hprev := st214_p67
  have hstep := st214_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p69 : ((1478452381111/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT214 (i+1))
      = (∑ i ∈ Finset.range 68, stT214 (i+1)) + stT214 69 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 68
    simpa using h
  have hprev := st214_p68
  have hstep := st214_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p70 : ((885146112083/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT214 (i+1))
      = (∑ i ∈ Finset.range 69, stT214 (i+1)) + stT214 70 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 69
    simpa using h
  have hprev := st214_p69
  have hstep := st214_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p71 : ((7509545806081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT214 (i+1))
      = (∑ i ∈ Finset.range 70, stT214 (i+1)) + stT214 71 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 70
    simpa using h
  have hprev := st214_p70
  have hstep := st214_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p72 : ((1385216909917/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT214 (i+1))
      = (∑ i ∈ Finset.range 71, stT214 (i+1)) + stT214 72 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 71
    simpa using h
  have hprev := st214_p71
  have hstep := st214_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p73 : ((960861875599/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT214 (i+1))
      = (∑ i ∈ Finset.range 72, stT214 (i+1)) + stT214 73 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 72
    simpa using h
  have hprev := st214_p72
  have hstep := st214_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p74 : ((6749653735927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT214 (i+1))
      = (∑ i ∈ Finset.range 73, stT214 (i+1)) + stT214 74 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 73
    simpa using h
  have hprev := st214_p73
  have hstep := st214_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p75 : ((7828618117627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT214 (i+1))
      = (∑ i ∈ Finset.range 74, stT214 (i+1)) + stT214 75 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 74
    simpa using h
  have hprev := st214_p74
  have hstep := st214_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p76 : ((6683340031657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT214 (i+1))
      = (∑ i ∈ Finset.range 75, stT214 (i+1)) + stT214 76 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 75
    simpa using h
  have hprev := st214_p75
  have hstep := st214_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p77 : ((1944050463343/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT214 (i+1))
      = (∑ i ∈ Finset.range 76, stT214 (i+1)) + stT214 77 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 76
    simpa using h
  have hprev := st214_p76
  have hstep := st214_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p78 : ((3443441202611/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT214 (i+1))
      = (∑ i ∈ Finset.range 77, stT214 (i+1)) + stT214 78 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 77
    simpa using h
  have hprev := st214_p77
  have hstep := st214_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p79 : ((7414191555643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT214 (i+1))
      = (∑ i ∈ Finset.range 78, stT214 (i+1)) + stT214 79 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 78
    simpa using h
  have hprev := st214_p78
  have hstep := st214_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p80 : ((1474303910393/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT214 (i+1))
      = (∑ i ∈ Finset.range 79, stT214 (i+1)) + stT214 80 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 79
    simpa using h
  have hprev := st214_p79
  have hstep := st214_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p81 : ((1378624944961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT214 (i+1))
      = (∑ i ∈ Finset.range 80, stT214 (i+1)) + stT214 81 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 80
    simpa using h
  have hprev := st214_p80
  have hstep := st214_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p82 : ((194956222667/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT214 (i+1))
      = (∑ i ∈ Finset.range 81, stT214 (i+1)) + stT214 82 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 81
    simpa using h
  have hprev := st214_p81
  have hstep := st214_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p83 : ((6702683744879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT214 (i+1))
      = (∑ i ∈ Finset.range 82, stT214 (i+1)) + stT214 83 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 82
    simpa using h
  have hprev := st214_p82
  have hstep := st214_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p84 : ((1530293274193/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT214 (i+1))
      = (∑ i ∈ Finset.range 83, stT214 (i+1)) + stT214 84 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 83
    simpa using h
  have hprev := st214_p83
  have hstep := st214_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p85 : ((3592051746877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT214 (i+1))
      = (∑ i ∈ Finset.range 84, stT214 (i+1)) + stT214 85 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 84
    simpa using h
  have hprev := st214_p84
  have hstep := st214_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p86 : ((3488489664921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT214 (i+1))
      = (∑ i ∈ Finset.range 85, stT214 (i+1)) + stT214 86 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 85
    simpa using h
  have hprev := st214_p85
  have hstep := st214_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p87 : ((3894984682113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT214 (i+1))
      = (∑ i ∈ Finset.range 86, stT214 (i+1)) + stT214 87 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 86
    simpa using h
  have hprev := st214_p86
  have hstep := st214_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p88 : ((3362009332213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT214 (i+1))
      = (∑ i ∈ Finset.range 87, stT214 (i+1)) + stT214 88 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 87
    simpa using h
  have hprev := st214_p87
  have hstep := st214_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p89 : ((3764140394103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT214 (i+1))
      = (∑ i ∈ Finset.range 88, stT214 (i+1)) + stT214 89 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 88
    simpa using h
  have hprev := st214_p88
  have hstep := st214_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p90 : ((7411519960689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT214 (i+1))
      = (∑ i ∈ Finset.range 89, stT214 (i+1)) + stT214 90 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 89
    simpa using h
  have hprev := st214_p89
  have hstep := st214_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p91 : ((6763807721459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT214 (i+1))
      = (∑ i ∈ Finset.range 90, stT214 (i+1)) + stT214 91 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 90
    simpa using h
  have hprev := st214_p90
  have hstep := st214_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p92 : ((1560180826663/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT214 (i+1))
      = (∑ i ∈ Finset.range 91, stT214 (i+1)) + stT214 92 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 91
    simpa using h
  have hprev := st214_p91
  have hstep := st214_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p93 : ((7025394693267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT214 (i+1))
      = (∑ i ∈ Finset.range 92, stT214 (i+1)) + stT214 93 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 92
    simpa using h
  have hprev := st214_p92
  have hstep := st214_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p94 : ((7017071117727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT214 (i+1))
      = (∑ i ∈ Finset.range 93, stT214 (i+1)) + stT214 94 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 93
    simpa using h
  have hprev := st214_p93
  have hstep := st214_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p95 : ((7811067284103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT214 (i+1))
      = (∑ i ∈ Finset.range 94, stT214 (i+1)) + stT214 95 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 94
    simpa using h
  have hprev := st214_p94
  have hstep := st214_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p96 : ((6813889948473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT214 (i+1))
      = (∑ i ∈ Finset.range 95, stT214 (i+1)) + stT214 96 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 95
    simpa using h
  have hprev := st214_p95
  have hstep := st214_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p97 : ((57910595469/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT214 (i+1))
      = (∑ i ∈ Finset.range 96, stT214 (i+1)) + stT214 97 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 96
    simpa using h
  have hprev := st214_p96
  have hstep := st214_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p98 : ((7736168730217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT214 (i+1))
      = (∑ i ∈ Finset.range 97, stT214 (i+1)) + stT214 98 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 97
    simpa using h
  have hprev := st214_p97
  have hstep := st214_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p99 : ((6734879521957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT214 (i+1))
      = (∑ i ∈ Finset.range 98, stT214 (i+1)) + stT214 99 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 98
    simpa using h
  have hprev := st214_p98
  have hstep := st214_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p100 : ((3676708951709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT214 (i+1))
      = (∑ i ∈ Finset.range 99, stT214 (i+1)) + stT214 100 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 99
    simpa using h
  have hprev := st214_p99
  have hstep := st214_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p101 : ((7690131458959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT214 (i+1))
      = (∑ i ∈ Finset.range 100, stT214 (i+1)) + stT214 101 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 100
    simpa using h
  have hprev := st214_p100
  have hstep := st214_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p102 : ((6718191290531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT214 (i+1))
      = (∑ i ∈ Finset.range 101, stT214 (i+1)) + stT214 102 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 101
    simpa using h
  have hprev := st214_p101
  have hstep := st214_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p103 : ((919990161037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT214 (i+1))
      = (∑ i ∈ Finset.range 102, stT214 (i+1)) + stT214 103 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 102
    simpa using h
  have hprev := st214_p102
  have hstep := st214_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p104 : ((1927381623779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT214 (i+1))
      = (∑ i ∈ Finset.range 103, stT214 (i+1)) + stT214 104 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 103
    simpa using h
  have hprev := st214_p103
  have hstep := st214_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p105 : ((1347948683697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT214 (i+1))
      = (∑ i ∈ Finset.range 104, stT214 (i+1)) + stT214 105 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 104
    simpa using h
  have hprev := st214_p104
  have hstep := st214_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p106 : ((1452785689971/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT214 (i+1))
      = (∑ i ∈ Finset.range 105, stT214 (i+1)) + stT214 106 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 105
    simpa using h
  have hprev := st214_p105
  have hstep := st214_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p107 : ((7779079829327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT214 (i+1))
      = (∑ i ∈ Finset.range 106, stT214 (i+1)) + stT214 107 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 106
    simpa using h
  have hprev := st214_p106
  have hstep := st214_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p108 : ((13332978551/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT214 (i+1))
      = (∑ i ∈ Finset.range 107, stT214 (i+1)) + stT214 108 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 107
    simpa using h
  have hprev := st214_p107
  have hstep := st214_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p109 : ((3536067889427/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT214 (i+1))
      = (∑ i ∈ Finset.range 108, stT214 (i+1)) + stT214 109 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 108
    simpa using h
  have hprev := st214_p108
  have hstep := st214_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p110 : ((1958789511571/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT214 (i+1))
      = (∑ i ∈ Finset.range 109, stT214 (i+1)) + stT214 110 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 109
    simpa using h
  have hprev := st214_p109
  have hstep := st214_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p111 : ((54936799289/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT214 (i+1))
      = (∑ i ∈ Finset.range 110, stT214 (i+1)) + stT214 111 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 110
    simpa using h
  have hprev := st214_p110
  have hstep := st214_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p112 : ((426980983753/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT214 (i+1))
      = (∑ i ∈ Finset.range 111, stT214 (i+1)) + stT214 112 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 111
    simpa using h
  have hprev := st214_p111
  have hstep := st214_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p113 : ((7583816287/9765625000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT214 (i+1))
      = (∑ i ∈ Finset.range 112, stT214 (i+1)) + stT214 113 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 112
    simpa using h
  have hprev := st214_p112
  have hstep := st214_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p114 : ((230408629947/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT214 (i+1))
      = (∑ i ∈ Finset.range 113, stT214 (i+1)) + stT214 114 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 113
    simpa using h
  have hprev := st214_p113
  have hstep := st214_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p115 : ((6678700297629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT214 (i+1))
      = (∑ i ∈ Finset.range 114, stT214 (i+1)) + stT214 115 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 114
    simpa using h
  have hprev := st214_p114
  have hstep := st214_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p116 : ((7466345057949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT214 (i+1))
      = (∑ i ∈ Finset.range 115, stT214 (i+1)) + stT214 116 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 115
    simpa using h
  have hprev := st214_p115
  have hstep := st214_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p117 : ((7732221088449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT214 (i+1))
      = (∑ i ∈ Finset.range 116, stT214 (i+1)) + stT214 117 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 116
    simpa using h
  have hprev := st214_p116
  have hstep := st214_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p118 : ((212886983407/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT214 (i+1))
      = (∑ i ∈ Finset.range 117, stT214 (i+1)) + stT214 118 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 117
    simpa using h
  have hprev := st214_p117
  have hstep := st214_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p119 : ((1747229834117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT214 (i+1))
      = (∑ i ∈ Finset.range 118, stT214 (i+1)) + stT214 119 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 118
    simpa using h
  have hprev := st214_p118
  have hstep := st214_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p120 : ((978084444511/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT214 (i+1))
      = (∑ i ∈ Finset.range 119, stT214 (i+1)) + stT214 120 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 119
    simpa using h
  have hprev := st214_p119
  have hstep := st214_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p121 : ((1824287966743/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT214 (i+1))
      = (∑ i ∈ Finset.range 120, stT214 (i+1)) + stT214 121 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 120
    simpa using h
  have hprev := st214_p120
  have hstep := st214_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p122 : ((13345119737/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT214 (i+1))
      = (∑ i ∈ Finset.range 121, stT214 (i+1)) + stT214 122 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 121
    simpa using h
  have hprev := st214_p121
  have hstep := st214_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p123 : ((3712096475119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT214 (i+1))
      = (∑ i ∈ Finset.range 122, stT214 (i+1)) + stT214 123 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 122
    simpa using h
  have hprev := st214_p122
  have hstep := st214_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p124 : ((3896436068191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT214 (i+1))
      = (∑ i ∈ Finset.range 123, stT214 (i+1)) + stT214 124 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 123
    simpa using h
  have hprev := st214_p123
  have hstep := st214_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p125 : ((3466005115183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT214 (i+1))
      = (∑ i ∈ Finset.range 124, stT214 (i+1)) + stT214 125 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 124
    simpa using h
  have hprev := st214_p124
  have hstep := st214_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p126 : ((6807111007037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT214 (i+1))
      = (∑ i ∈ Finset.range 125, stT214 (i+1)) + stT214 126 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 125
    simpa using h
  have hprev := st214_p125
  have hstep := st214_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p127 : ((7694250492173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT214 (i+1))
      = (∑ i ∈ Finset.range 126, stT214 (i+1)) + stT214 127 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 126
    simpa using h
  have hprev := st214_p126
  have hstep := st214_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p128 : ((7616585372861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT214 (i+1))
      = (∑ i ∈ Finset.range 127, stT214 (i+1)) + stT214 128 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 127
    simpa using h
  have hprev := st214_p127
  have hstep := st214_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p129 : ((6750716402323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT214 (i+1))
      = (∑ i ∈ Finset.range 128, stT214 (i+1)) + stT214 129 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 128
    simpa using h
  have hprev := st214_p128
  have hstep := st214_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p130 : ((6979736418457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT214 (i+1))
      = (∑ i ∈ Finset.range 129, stT214 (i+1)) + stT214 130 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 129
    simpa using h
  have hprev := st214_p129
  have hstep := st214_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p131 : ((312212567241/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT214 (i+1))
      = (∑ i ∈ Finset.range 130, stT214 (i+1)) + stT214 131 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 130
    simpa using h
  have hprev := st214_p130
  have hstep := st214_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p132 : ((1868611779433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT214 (i+1))
      = (∑ i ∈ Finset.range 131, stT214 (i+1)) + stT214 132 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 131
    simpa using h
  have hprev := st214_p131
  have hstep := st214_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p133 : ((3343876883121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT214 (i+1))
      = (∑ i ∈ Finset.range 132, stT214 (i+1)) + stT214 133 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 132
    simpa using h
  have hprev := st214_p132
  have hstep := st214_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p134 : ((707616696027/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT214 (i+1))
      = (∑ i ∈ Finset.range 133, stT214 (i+1)) + stT214 134 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 133
    simpa using h
  have hprev := st214_p133
  have hstep := st214_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p135 : ((156737089247/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT214 (i+1))
      = (∑ i ∈ Finset.range 134, stT214 (i+1)) + stT214 135 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 134
    simpa using h
  have hprev := st214_p134
  have hstep := st214_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p136 : ((742930518931/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT214 (i+1))
      = (∑ i ∈ Finset.range 135, stT214 (i+1)) + stT214 136 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 135
    simpa using h
  have hprev := st214_p135
  have hstep := st214_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p137 : ((1669081540987/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT214 (i+1))
      = (∑ i ∈ Finset.range 136, stT214 (i+1)) + stT214 137 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 136
    simpa using h
  have hprev := st214_p136
  have hstep := st214_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p138 : ((1766923841557/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT214 (i+1))
      = (∑ i ∈ Finset.range 137, stT214 (i+1)) + stT214 138 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 137
    simpa using h
  have hprev := st214_p137
  have hstep := st214_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p139 : ((978826984347/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT214 (i+1))
      = (∑ i ∈ Finset.range 138, stT214 (i+1)) + stT214 139 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 138
    simpa using h
  have hprev := st214_p138
  have hstep := st214_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p140 : ((3744758193853/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT214 (i+1))
      = (∑ i ∈ Finset.range 139, stT214 (i+1)) + stT214 140 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 139
    simpa using h
  have hprev := st214_p139
  have hstep := st214_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p141 : ((3351809228501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT214 (i+1))
      = (∑ i ∈ Finset.range 140, stT214 (i+1)) + stT214 141 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 140
    simpa using h
  have hprev := st214_p140
  have hstep := st214_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p142 : ((3479507401271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT214 (i+1))
      = (∑ i ∈ Finset.range 141, stT214 (i+1)) + stT214 142 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 141
    simpa using h
  have hprev := st214_p141
  have hstep := st214_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p143 : ((31084772411/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT214 (i+1))
      = (∑ i ∈ Finset.range 142, stT214 (i+1)) + stT214 143 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 142
    simpa using h
  have hprev := st214_p142
  have hstep := st214_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p144 : ((1909441790669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT214 (i+1))
      = (∑ i ∈ Finset.range 143, stT214 (i+1)) + stT214 144 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 143
    simpa using h
  have hprev := st214_p143
  have hstep := st214_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p145 : ((6809359234251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT214 (i+1))
      = (∑ i ∈ Finset.range 144, stT214 (i+1)) + stT214 145 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 144
    simpa using h
  have hprev := st214_p144
  have hstep := st214_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p146 : ((6785276727257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT214 (i+1))
      = (∑ i ∈ Finset.range 145, stT214 (i+1)) + stT214 146 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 145
    simpa using h
  have hprev := st214_p145
  have hstep := st214_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p147 : ((7602054055197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT214 (i+1))
      = (∑ i ∈ Finset.range 146, stT214 (i+1)) + stT214 147 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 146
    simpa using h
  have hprev := st214_p146
  have hstep := st214_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p148 : ((7812574938537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT214 (i+1))
      = (∑ i ∈ Finset.range 147, stT214 (i+1)) + stT214 148 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 147
    simpa using h
  have hprev := st214_p147
  have hstep := st214_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p149 : ((7054428972617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT214 (i+1))
      = (∑ i ∈ Finset.range 148, stT214 (i+1)) + stT214 149 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 148
    simpa using h
  have hprev := st214_p148
  have hstep := st214_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p150 : ((6642948777491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT214 (i+1))
      = (∑ i ∈ Finset.range 149, stT214 (i+1)) + stT214 150 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 149
    simpa using h
  have hprev := st214_p149
  have hstep := st214_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p151 : ((7277235489391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT214 (i+1))
      = (∑ i ∈ Finset.range 150, stT214 (i+1)) + stT214 151 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 150
    simpa using h
  have hprev := st214_p150
  have hstep := st214_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p152 : ((1575716746067/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT214 (i+1))
      = (∑ i ∈ Finset.range 151, stT214 (i+1)) + stT214 152 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 151
    simpa using h
  have hprev := st214_p151
  have hstep := st214_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p153 : ((7443592359873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT214 (i+1))
      = (∑ i ∈ Finset.range 152, stT214 (i+1)) + stT214 153 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 152
    simpa using h
  have hprev := st214_p152
  have hstep := st214_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p154 : ((1674668567009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT214 (i+1))
      = (∑ i ∈ Finset.range 153, stT214 (i+1)) + stT214 154 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 153
    simpa using h
  have hprev := st214_p153
  have hstep := st214_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p155 : ((6862721306939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT214 (i+1))
      = (∑ i ∈ Finset.range 154, stT214 (i+1)) + stT214 155 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 154
    simpa using h
  have hprev := st214_p154
  have hstep := st214_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p156 : ((7663271635259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT214 (i+1))
      = (∑ i ∈ Finset.range 155, stT214 (i+1)) + stT214 156 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 155
    simpa using h
  have hprev := st214_p155
  have hstep := st214_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p157 : ((7815702070829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT214 (i+1))
      = (∑ i ∈ Finset.range 156, stT214 (i+1)) + stT214 157 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 156
    simpa using h
  have hprev := st214_p156
  have hstep := st214_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p158 : ((7084242178889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT214 (i+1))
      = (∑ i ∈ Finset.range 157, stT214 (i+1)) + stT214 158 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 157
    simpa using h
  have hprev := st214_p157
  have hstep := st214_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p159 : ((6620240142521/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT214 (i+1))
      = (∑ i ∈ Finset.range 158, stT214 (i+1)) + stT214 159 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 158
    simpa using h
  have hprev := st214_p158
  have hstep := st214_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p160 : ((7139568080897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT214 (i+1))
      = (∑ i ∈ Finset.range 159, stT214 (i+1)) + stT214 160 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 159
    simpa using h
  have hprev := st214_p159
  have hstep := st214_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p161 : ((7838832076267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT214 (i+1))
      = (∑ i ∈ Finset.range 160, stT214 (i+1)) + stT214 161 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 160
    simpa using h
  have hprev := st214_p160
  have hstep := st214_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p162 : ((7656927886217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT214 (i+1))
      = (∑ i ∈ Finset.range 161, stT214 (i+1)) + stT214 162 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 161
    simpa using h
  have hprev := st214_p161
  have hstep := st214_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p163 : ((859223536459/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT214 (i+1))
      = (∑ i ∈ Finset.range 162, stT214 (i+1)) + stT214 163 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 162
    simpa using h
  have hprev := st214_p162
  have hstep := st214_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p164 : ((1664075945317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT214 (i+1))
      = (∑ i ∈ Finset.range 163, stT214 (i+1)) + stT214 164 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 163
    simpa using h
  have hprev := st214_p163
  have hstep := st214_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p165 : ((28590245959/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT214 (i+1))
      = (∑ i ∈ Finset.range 164, stT214 (i+1)) + stT214 165 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 164
    simpa using h
  have hprev := st214_p164
  have hstep := st214_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p166 : ((3945860411277/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT214 (i+1))
      = (∑ i ∈ Finset.range 165, stT214 (i+1)) + stT214 166 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 165
    simpa using h
  have hprev := st214_p165
  have hstep := st214_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p167 : ((3775643119821/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT214 (i+1))
      = (∑ i ∈ Finset.range 166, stT214 (i+1)) + stT214 167 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 166
    simpa using h
  have hprev := st214_p166
  have hstep := st214_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p168 : ((3394933427069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT214 (i+1))
      = (∑ i ∈ Finset.range 167, stT214 (i+1)) + stT214 168 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 167
    simpa using h
  have hprev := st214_p167
  have hstep := st214_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p169 : ((167091324403/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT214 (i+1))
      = (∑ i ∈ Finset.range 168, stT214 (i+1)) + stT214 169 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 168
    simpa using h
  have hprev := st214_p168
  have hstep := st214_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p170 : ((460956990551/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT214 (i+1))
      = (∑ i ∈ Finset.range 169, stT214 (i+1)) + stT214 170 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 169
    simpa using h
  have hprev := st214_p169
  have hstep := st214_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p171 : ((790343137853/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT214 (i+1))
      = (∑ i ∈ Finset.range 170, stT214 (i+1)) + stT214 171 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 170
    simpa using h
  have hprev := st214_p170
  have hstep := st214_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p172 : ((7547631557419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT214 (i+1))
      = (∑ i ∈ Finset.range 171, stT214 (i+1)) + stT214 172 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 171
    simpa using h
  have hprev := st214_p171
  have hstep := st214_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p173 : ((6796445420553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT214 (i+1))
      = (∑ i ∈ Finset.range 172, stT214 (i+1)) + stT214 173 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 172
    simpa using h
  have hprev := st214_p172
  have hstep := st214_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p174 : ((6659071816961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT214 (i+1))
      = (∑ i ∈ Finset.range 173, stT214 (i+1)) + stT214 174 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 173
    simpa using h
  have hprev := st214_p173
  have hstep := st214_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p175 : ((7312553430689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT214 (i+1))
      = (∑ i ∈ Finset.range 174, stT214 (i+1)) + stT214 175 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 174
    simpa using h
  have hprev := st214_p174
  have hstep := st214_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p176 : ((7892527560783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT214 (i+1))
      = (∑ i ∈ Finset.range 175, stT214 (i+1)) + stT214 176 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 175
    simpa using h
  have hprev := st214_p175
  have hstep := st214_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p177 : ((3822875287989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT214 (i+1))
      = (∑ i ∈ Finset.range 176, stT214 (i+1)) + stT214 177 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 176
    simpa using h
  have hprev := st214_p176
  have hstep := st214_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p178 : ((137930682579/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT214 (i+1))
      = (∑ i ∈ Finset.range 177, stT214 (i+1)) + stT214 178 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 177
    simpa using h
  have hprev := st214_p177
  have hstep := st214_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p179 : ((3301820807841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT214 (i+1))
      = (∑ i ∈ Finset.range 178, stT214 (i+1)) + stT214 179 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 178
    simpa using h
  have hprev := st214_p178
  have hstep := st214_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p180 : ((7132856336717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT214 (i+1))
      = (∑ i ∈ Finset.range 179, stT214 (i+1)) + stT214 180 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 179
    simpa using h
  have hprev := st214_p179
  have hstep := st214_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p181 : ((7816158334683/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT214 (i+1))
      = (∑ i ∈ Finset.range 180, stT214 (i+1)) + stT214 181 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 180
    simpa using h
  have hprev := st214_p180
  have hstep := st214_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p182 : ((7806739270933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT214 (i+1))
      = (∑ i ∈ Finset.range 181, stT214 (i+1)) + stT214 182 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 181
    simpa using h
  have hprev := st214_p181
  have hstep := st214_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p183 : ((7121738465411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT214 (i+1))
      = (∑ i ∈ Finset.range 182, stT214 (i+1)) + stT214 183 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 182
    simpa using h
  have hprev := st214_p182
  have hstep := st214_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p184 : ((6597966241821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT214 (i+1))
      = (∑ i ∈ Finset.range 183, stT214 (i+1)) + stT214 184 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 183
    simpa using h
  have hprev := st214_p183
  have hstep := st214_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p185 : ((6863652730643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT214 (i+1))
      = (∑ i ∈ Finset.range 184, stT214 (i+1)) + stT214 185 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 184
    simpa using h
  have hprev := st214_p184
  have hstep := st214_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p186 : ((7596028379223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT214 (i+1))
      = (∑ i ∈ Finset.range 185, stT214 (i+1)) + stT214 186 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 185
    simpa using h
  have hprev := st214_p185
  have hstep := st214_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p187 : ((7927630980343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT214 (i+1))
      = (∑ i ∈ Finset.range 186, stT214 (i+1)) + stT214 187 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 186
    simpa using h
  have hprev := st214_p186
  have hstep := st214_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p188 : ((1868583950267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT214 (i+1))
      = (∑ i ∈ Finset.range 187, stT214 (i+1)) + stT214 188 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 187
    simpa using h
  have hprev := st214_p187
  have hstep := st214_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p189 : ((338345996121/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT214 (i+1))
      = (∑ i ∈ Finset.range 188, stT214 (i+1)) + stT214 189 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 188
    simpa using h
  have hprev := st214_p188
  have hstep := st214_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p190 : ((264728320783/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT214 (i+1))
      = (∑ i ∈ Finset.range 189, stT214 (i+1)) + stT214 190 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 189
    simpa using h
  have hprev := st214_p189
  have hstep := st214_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p191 : ((1438503911397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT214 (i+1))
      = (∑ i ∈ Finset.range 190, stT214 (i+1)) + stT214 191 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 190
    simpa using h
  have hprev := st214_p190
  have hstep := st214_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p192 : ((313518990367/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT214 (i+1))
      = (∑ i ∈ Finset.range 191, stT214 (i+1)) + stT214 192 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 191
    simpa using h
  have hprev := st214_p191
  have hstep := st214_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p193 : ((7834659286679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT214 (i+1))
      = (∑ i ∈ Finset.range 192, stT214 (i+1)) + stT214 193 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 192
    simpa using h
  have hprev := st214_p192
  have hstep := st214_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p194 : ((7191386689613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT214 (i+1))
      = (∑ i ∈ Finset.range 193, stT214 (i+1)) + stT214 194 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 193
    simpa using h
  have hprev := st214_p193
  have hstep := st214_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p195 : ((1654236433217/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT214 (i+1))
      = (∑ i ∈ Finset.range 194, stT214 (i+1)) + stT214 195 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 194
    simpa using h
  have hprev := st214_p194
  have hstep := st214_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p196 : ((6733392044993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT214 (i+1))
      = (∑ i ∈ Finset.range 195, stT214 (i+1)) + stT214 196 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 195
    simpa using h
  have hprev := st214_p195
  have hstep := st214_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p197 : ((7410122412383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT214 (i+1))
      = (∑ i ∈ Finset.range 196, stT214 (i+1)) + stT214 197 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 196
    simpa using h
  have hprev := st214_p196
  have hstep := st214_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p198 : ((7922443694483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT214 (i+1))
      = (∑ i ∈ Finset.range 197, stT214 (i+1)) + stT214 198 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 197
    simpa using h
  have hprev := st214_p197
  have hstep := st214_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p199 : ((7731335487221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT214 (i+1))
      = (∑ i ∈ Finset.range 198, stT214 (i+1)) + stT214 199 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 198
    simpa using h
  have hprev := st214_p198
  have hstep := st214_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p200 : ((1408409799567/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT214 (i+1))
      = (∑ i ∈ Finset.range 199, stT214 (i+1)) + stT214 200 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 199
    simpa using h
  have hprev := st214_p199
  have hstep := st214_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p201 : ((6572347105553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT214 (i+1))
      = (∑ i ∈ Finset.range 200, stT214 (i+1)) + stT214 201 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 200
    simpa using h
  have hprev := st214_p200
  have hstep := st214_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p202 : ((6802544343237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT214 (i+1))
      = (∑ i ∈ Finset.range 201, stT214 (i+1)) + stT214 202 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 201
    simpa using h
  have hprev := st214_p201
  have hstep := st214_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p203 : ((1498590250707/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT214 (i+1))
      = (∑ i ∈ Finset.range 202, stT214 (i+1)) + stT214 203 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 202
    simpa using h
  have hprev := st214_p202
  have hstep := st214_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p204 : ((1588774303911/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT214 (i+1))
      = (∑ i ∈ Finset.range 203, stT214 (i+1)) + stT214 204 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 203
    simpa using h
  have hprev := st214_p203
  have hstep := st214_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p205 : ((120415055053/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT214 (i+1))
      = (∑ i ∈ Finset.range 204, stT214 (i+1)) + stT214 205 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 204
    simpa using h
  have hprev := st214_p204
  have hstep := st214_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p206 : ((3510702182667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT214 (i+1))
      = (∑ i ∈ Finset.range 205, stT214 (i+1)) + stT214 206 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 205
    simpa using h
  have hprev := st214_p205
  have hstep := st214_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p207 : ((6564484018077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT214 (i+1))
      = (∑ i ∈ Finset.range 206, stT214 (i+1)) + stT214 207 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 206
    simpa using h
  have hprev := st214_p206
  have hstep := st214_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p208 : ((1694659435113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT214 (i+1))
      = (∑ i ∈ Finset.range 207, stT214 (i+1)) + stT214 208 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 207
    simpa using h
  have hprev := st214_p207
  have hstep := st214_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p209 : ((3726022073007/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT214 (i+1))
      = (∑ i ∈ Finset.range 208, stT214 (i+1)) + stT214 209 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 208
    simpa using h
  have hprev := st214_p208
  have hstep := st214_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p210 : ((3968579920507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT214 (i+1))
      = (∑ i ∈ Finset.range 209, stT214 (i+1)) + stT214 210 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 209
    simpa using h
  have hprev := st214_p209
  have hstep := st214_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p211 : ((311020916307/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT214 (i+1))
      = (∑ i ∈ Finset.range 210, stT214 (i+1)) + stT214 211 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 210
    simpa using h
  have hprev := st214_p210
  have hstep := st214_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p212 : ((356199533787/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT214 (i+1))
      = (∑ i ∈ Finset.range 211, stT214 (i+1)) + stT214 212 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 211
    simpa using h
  have hprev := st214_p211
  have hstep := st214_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p213 : ((6593346739879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT214 (i+1))
      = (∑ i ∈ Finset.range 212, stT214 (i+1)) + stT214 213 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 212
    simpa using h
  have hprev := st214_p212
  have hstep := st214_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p214 : ((6672831269339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT214 (i+1))
      = (∑ i ∈ Finset.range 213, stT214 (i+1)) + stT214 214 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 213
    simpa using h
  have hprev := st214_p213
  have hstep := st214_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p215 : ((1456988814427/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT214 (i+1))
      = (∑ i ∈ Finset.range 214, stT214 (i+1)) + stT214 215 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 214
    simpa using h
  have hprev := st214_p214
  have hstep := st214_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p216 : ((1967431086143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT214 (i+1))
      = (∑ i ∈ Finset.range 215, stT214 (i+1)) + stT214 216 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 215
    simpa using h
  have hprev := st214_p215
  have hstep := st214_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p217 : ((493800071503/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT214 (i+1))
      = (∑ i ∈ Finset.range 216, stT214 (i+1)) + stT214 217 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 216
    simpa using h
  have hprev := st214_p216
  have hstep := st214_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p218 : ((459662147959/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT214 (i+1))
      = (∑ i ∈ Finset.range 217, stT214 (i+1)) + stT214 218 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 217
    simpa using h
  have hprev := st214_p217
  have hstep := st214_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p219 : ((839878117127/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT214 (i+1))
      = (∑ i ∈ Finset.range 218, stT214 (i+1)) + stT214 219 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 218
    simpa using h
  have hprev := st214_p218
  have hstep := st214_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p220 : ((819091351277/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT214 (i+1))
      = (∑ i ∈ Finset.range 219, stT214 (i+1)) + stT214 220 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 219
    simpa using h
  have hprev := st214_p219
  have hstep := st214_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p221 : ((874616641097/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT214 (i+1))
      = (∑ i ∈ Finset.range 220, stT214 (i+1)) + stT214 221 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 220
    simpa using h
  have hprev := st214_p220
  have hstep := st214_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p222 : ((239484115943/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT214 (i+1))
      = (∑ i ∈ Finset.range 221, stT214 (i+1)) + stT214 222 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 221
    simpa using h
  have hprev := st214_p221
  have hstep := st214_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p223 : ((1595995038743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT214 (i+1))
      = (∑ i ∈ Finset.range 222, stT214 (i+1)) + stT214 223 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 222
    simpa using h
  have hprev := st214_p222
  have hstep := st214_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p224 : ((7680211910539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT214 (i+1))
      = (∑ i ∈ Finset.range 223, stT214 (i+1)) + stT214 224 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 223
    simpa using h
  have hprev := st214_p223
  have hstep := st214_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p225 : ((438827182149/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT214 (i+1))
      = (∑ i ∈ Finset.range 224, stT214 (i+1)) + stT214 225 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 224
    simpa using h
  have hprev := st214_p224
  have hstep := st214_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p226 : ((3278076661457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT214 (i+1))
      = (∑ i ∈ Finset.range 225, stT214 (i+1)) + stT214 226 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 225
    simpa using h
  have hprev := st214_p225
  have hstep := st214_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p227 : ((833604860801/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT214 (i+1))
      = (∑ i ∈ Finset.range 226, stT214 (i+1)) + stT214 227 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 226
    simpa using h
  have hprev := st214_p226
  have hstep := st214_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p228 : ((181559571703/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT214 (i+1))
      = (∑ i ∈ Finset.range 227, stT214 (i+1)) + stT214 228 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 227
    simpa using h
  have hprev := st214_p227
  have hstep := st214_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p229 : ((981173106781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT214 (i+1))
      = (∑ i ∈ Finset.range 228, stT214 (i+1)) + stT214 229 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 228
    simpa using h
  have hprev := st214_p228
  have hstep := st214_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p230 : ((1988806968117/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT214 (i+1))
      = (∑ i ∈ Finset.range 229, stT214 (i+1)) + stT214 230 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 229
    simpa using h
  have hprev := st214_p229
  have hstep := st214_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p231 : ((1874629761261/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT214 (i+1))
      = (∑ i ∈ Finset.range 230, stT214 (i+1)) + stT214 231 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 230
    simpa using h
  have hprev := st214_p230
  have hstep := st214_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p232 : ((6846733435167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT214 (i+1))
      = (∑ i ∈ Finset.range 231, stT214 (i+1)) + stT214 232 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 231
    simpa using h
  have hprev := st214_p231
  have hstep := st214_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p233 : ((6515733699789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT214 (i+1))
      = (∑ i ∈ Finset.range 232, stT214 (i+1)) + stT214 233 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 232
    simpa using h
  have hprev := st214_p232
  have hstep := st214_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p234 : ((6762353492109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT214 (i+1))
      = (∑ i ∈ Finset.range 233, stT214 (i+1)) + stT214 234 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 233
    simpa using h
  have hprev := st214_p233
  have hstep := st214_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p235 : ((7390783455829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT214 (i+1))
      = (∑ i ∈ Finset.range 234, stT214 (i+1)) + stT214 235 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 234
    simpa using h
  have hprev := st214_p234
  have hstep := st214_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p236 : ((7913887261781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT214 (i+1))
      = (∑ i ∈ Finset.range 235, stT214 (i+1)) + stT214 236 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 235
    simpa using h
  have hprev := st214_p235
  have hstep := st214_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p237 : ((7932405174833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT214 (i+1))
      = (∑ i ∈ Finset.range 236, stT214 (i+1)) + stT214 237 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 236
    simpa using h
  have hprev := st214_p236
  have hstep := st214_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p238 : ((7435894523117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT214 (i+1))
      = (∑ i ∈ Finset.range 237, stT214 (i+1)) + stT214 238 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 237
    simpa using h
  have hprev := st214_p237
  have hstep := st214_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p239 : ((680177682523/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT214 (i+1))
      = (∑ i ∈ Finset.range 238, stT214 (i+1)) + stT214 239 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 238
    simpa using h
  have hprev := st214_p238
  have hstep := st214_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p240 : ((1626161426089/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT214 (i+1))
      = (∑ i ∈ Finset.range 239, stT214 (i+1)) + stT214 240 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 239
    simpa using h
  have hprev := st214_p239
  have hstep := st214_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p241 : ((338113923659/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT214 (i+1))
      = (∑ i ∈ Finset.range 240, stT214 (i+1)) + stT214 241 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 240
    simpa using h
  have hprev := st214_p240
  have hstep := st214_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p242 : ((1845309890163/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT214 (i+1))
      = (∑ i ∈ Finset.range 241, stT214 (i+1)) + stT214 242 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 241
    simpa using h
  have hprev := st214_p241
  have hstep := st214_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p243 : ((494203665947/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT214 (i+1))
      = (∑ i ∈ Finset.range 242, stT214 (i+1)) + stT214 243 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 242
    simpa using h
  have hprev := st214_p242
  have hstep := st214_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p244 : ((995006748681/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT214 (i+1))
      = (∑ i ∈ Finset.range 243, stT214 (i+1)) + stT214 244 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 243
    simpa using h
  have hprev := st214_p243
  have hstep := st214_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p245 : ((938126251617/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT214 (i+1))
      = (∑ i ∈ Finset.range 244, stT214 (i+1)) + stT214 245 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 244
    simpa using h
  have hprev := st214_p244
  have hstep := st214_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p246 : ((6870187983153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT214 (i+1))
      = (∑ i ∈ Finset.range 245, stT214 (i+1)) + stT214 246 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 245
    simpa using h
  have hprev := st214_p245
  have hstep := st214_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p247 : ((3253058261499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT214 (i+1))
      = (∑ i ∈ Finset.range 246, stT214 (i+1)) + stT214 247 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 246
    simpa using h
  have hprev := st214_p246
  have hstep := st214_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p248 : ((3333296543999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT214 (i+1))
      = (∑ i ∈ Finset.range 247, stT214 (i+1)) + stT214 248 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 247
    simpa using h
  have hprev := st214_p247
  have hstep := st214_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p249 : ((3618030955233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT214 (i+1))
      = (∑ i ∈ Finset.range 248, stT214 (i+1)) + stT214 249 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 248
    simpa using h
  have hprev := st214_p248
  have hstep := st214_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p250 : ((7817660571461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT214 (i+1))
      = (∑ i ∈ Finset.range 249, stT214 (i+1)) + stT214 250 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 249
    simpa using h
  have hprev := st214_p249
  have hstep := st214_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p251 : ((8011906106603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT214 (i+1))
      = (∑ i ∈ Finset.range 250, stT214 (i+1)) + stT214 251 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 250
    simpa using h
  have hprev := st214_p250
  have hstep := st214_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p252 : ((7689073942923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT214 (i+1))
      = (∑ i ∈ Finset.range 251, stT214 (i+1)) + stT214 252 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 251
    simpa using h
  have hprev := st214_p251
  have hstep := st214_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p253 : ((3535552554159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT214 (i+1))
      = (∑ i ∈ Finset.range 252, stT214 (i+1)) + stT214 253 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 252
    simpa using h
  have hprev := st214_p252
  have hstep := st214_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p254 : ((657497690403/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT214 (i+1))
      = (∑ i ∈ Finset.range 253, stT214 (i+1)) + stT214 254 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 253
    simpa using h
  have hprev := st214_p253
  have hstep := st214_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p255 : ((1306104613991/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT214 (i+1))
      = (∑ i ∈ Finset.range 254, stT214 (i+1)) + stT214 255 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 254
    simpa using h
  have hprev := st214_p254
  have hstep := st214_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p256 : ((1392807613991/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT214 (i+1))
      = (∑ i ∈ Finset.range 255, stT214 (i+1)) + stT214 256 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 255
    simpa using h
  have hprev := st214_p255
  have hstep := st214_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p257 : ((7587506931391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT214 (i+1))
      = (∑ i ∈ Finset.range 256, stT214 (i+1)) + stT214 257 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 256
    simpa using h
  have hprev := st214_p256
  have hstep := st214_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p258 : ((7993121927971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT214 (i+1))
      = (∑ i ∈ Finset.range 257, stT214 (i+1)) + stT214 258 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 257
    simpa using h
  have hprev := st214_p257
  have hstep := st214_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p259 : ((7919807724411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT214 (i+1))
      = (∑ i ∈ Finset.range 258, stT214 (i+1)) + stT214 259 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 258
    simpa using h
  have hprev := st214_p258
  have hstep := st214_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p260 : ((7417897805341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT214 (i+1))
      = (∑ i ∈ Finset.range 259, stT214 (i+1)) + stT214 260 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 259
    simpa using h
  have hprev := st214_p259
  have hstep := st214_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p261 : ((6810444495891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT214 (i+1))
      = (∑ i ∈ Finset.range 260, stT214 (i+1)) + stT214 261 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 260
    simpa using h
  have hprev := st214_p260
  have hstep := st214_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p262 : ((6482848277111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT214 (i+1))
      = (∑ i ∈ Finset.range 261, stT214 (i+1)) + stT214 262 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 261
    simpa using h
  have hprev := st214_p261
  have hstep := st214_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p263 : ((6639184550021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT214 (i+1))
      = (∑ i ∈ Finset.range 262, stT214 (i+1)) + stT214 263 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 262
    simpa using h
  have hprev := st214_p262
  have hstep := st214_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p264 : ((71785999913/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT214 (i+1))
      = (∑ i ∈ Finset.range 263, stT214 (i+1)) + stT214 264 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 263
    simpa using h
  have hprev := st214_p263
  have hstep := st214_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p265 : ((24263056027/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT214 (i+1))
      = (∑ i ∈ Finset.range 264, stT214 (i+1)) + stT214 265 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 264
    simpa using h
  have hprev := st214_p264
  have hstep := st214_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p266 : ((4017612916907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT214 (i+1))
      = (∑ i ∈ Finset.range 265, stT214 (i+1)) + stT214 266 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 265
    simpa using h
  have hprev := st214_p265
  have hstep := st214_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p267 : ((7828200906343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT214 (i+1))
      = (∑ i ∈ Finset.range 266, stT214 (i+1)) + stT214 267 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 266
    simpa using h
  have hprev := st214_p266
  have hstep := st214_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p268 : ((7271856429991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT214 (i+1))
      = (∑ i ∈ Finset.range 267, stT214 (i+1)) + stT214 268 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 267
    simpa using h
  have hprev := st214_p267
  have hstep := st214_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p269 : ((6703653335449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT214 (i+1))
      = (∑ i ∈ Finset.range 268, stT214 (i+1)) + stT214 269 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 268
    simpa using h
  have hprev := st214_p268
  have hstep := st214_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p270 : ((100993242537/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT214 (i+1))
      = (∑ i ∈ Finset.range 269, stT214 (i+1)) + stT214 270 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 269
    simpa using h
  have hprev := st214_p269
  have hstep := st214_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p271 : ((41825300783/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT214 (i+1))
      = (∑ i ∈ Finset.range 270, stT214 (i+1)) + stT214 271 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 270
    simpa using h
  have hprev := st214_p270
  have hstep := st214_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p272 : ((1812804094109/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT214 (i+1))
      = (∑ i ∈ Finset.range 271, stT214 (i+1)) + stT214 272 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 271
    simpa using h
  have hprev := st214_p271
  have hstep := st214_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p273 : ((3905667904063/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT214 (i+1))
      = (∑ i ∈ Finset.range 272, stT214 (i+1)) + stT214 273 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 272
    simpa using h
  have hprev := st214_p272
  have hstep := st214_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p274 : ((502907871239/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT214 (i+1))
      = (∑ i ∈ Finset.range 273, stT214 (i+1)) + stT214 274 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 273
    simpa using h
  have hprev := st214_p273
  have hstep := st214_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p275 : ((7823020892081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT214 (i+1))
      = (∑ i ∈ Finset.range 274, stT214 (i+1)) + stT214 275 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 274
    simpa using h
  have hprev := st214_p274
  have hstep := st214_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p276 : ((7272003335341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT214 (i+1))
      = (∑ i ∈ Finset.range 275, stT214 (i+1)) + stT214 276 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 275
    simpa using h
  have hprev := st214_p275
  have hstep := st214_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p277 : ((1341912469849/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT214 (i+1))
      = (∑ i ∈ Finset.range 276, stT214 (i+1)) + stT214 277 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 276
    simpa using h
  have hprev := st214_p276
  have hstep := st214_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p278 : ((403378522897/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT214 (i+1))
      = (∑ i ∈ Finset.range 277, stT214 (i+1)) + stT214 278 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 277
    simpa using h
  have hprev := st214_p277
  have hstep := st214_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p279 : ((1661774457841/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT214 (i+1))
      = (∑ i ∈ Finset.range 278, stT214 (i+1)) + stT214 279 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 278
    simpa using h
  have hprev := st214_p278
  have hstep := st214_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p280 : ((3589019512727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT214 (i+1))
      = (∑ i ∈ Finset.range 279, stT214 (i+1)) + stT214 280 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 279
    simpa using h
  have hprev := st214_p279
  have hstep := st214_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p281 : ((1550060383823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT214 (i+1))
      = (∑ i ∈ Finset.range 280, stT214 (i+1)) + stT214 281 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 280
    simpa using h
  have hprev := st214_p280
  have hstep := st214_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p282 : ((8048449971031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT214 (i+1))
      = (∑ i ∈ Finset.range 281, stT214 (i+1)) + stT214 282 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 281
    simpa using h
  have hprev := st214_p281
  have hstep := st214_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p283 : ((7911119106617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT214 (i+1))
      = (∑ i ∈ Finset.range 282, stT214 (i+1)) + stT214 283 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 282
    simpa using h
  have hprev := st214_p282
  have hstep := st214_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p284 : ((7415669664731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT214 (i+1))
      = (∑ i ∈ Finset.range 283, stT214 (i+1)) + stT214 284 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 283
    simpa using h
  have hprev := st214_p283
  have hstep := st214_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p285 : ((1707940853757/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT214 (i+1))
      = (∑ i ∈ Finset.range 284, stT214 (i+1)) + stT214 285 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 284
    simpa using h
  have hprev := st214_p284
  have hstep := st214_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p286 : ((3236496856643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT214 (i+1))
      = (∑ i ∈ Finset.range 285, stT214 (i+1)) + stT214 286 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 285
    simpa using h
  have hprev := st214_p285
  have hstep := st214_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p287 : ((1632248417939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT214 (i+1))
      = (∑ i ∈ Finset.range 286, stT214 (i+1)) + stT214 287 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 286
    simpa using h
  have hprev := st214_p286
  have hstep := st214_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p288 : ((6967511939461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT214 (i+1))
      = (∑ i ∈ Finset.range 287, stT214 (i+1)) + stT214 288 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 287
    simpa using h
  have hprev := st214_p287
  have hstep := st214_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p289 : ((7555685763021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT214 (i+1))
      = (∑ i ∈ Finset.range 288, stT214 (i+1)) + stT214 289 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 288
    simpa using h
  have hprev := st214_p288
  have hstep := st214_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p290 : ((7985483238201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT214 (i+1))
      = (∑ i ∈ Finset.range 289, stT214 (i+1)) + stT214 290 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 289
    simpa using h
  have hprev := st214_p289
  have hstep := st214_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p291 : ((8034961707041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT214 (i+1))
      = (∑ i ∈ Finset.range 290, stT214 (i+1)) + stT214 291 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 290
    simpa using h
  have hprev := st214_p290
  have hstep := st214_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p292 : ((7680962989963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT214 (i+1))
      = (∑ i ∈ Finset.range 291, stT214 (i+1)) + stT214 292 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 291
    simpa using h
  have hprev := st214_p291
  have hstep := st214_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p293 : ((444199626027/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT214 (i+1))
      = (∑ i ∈ Finset.range 292, stT214 (i+1)) + stT214 293 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 292
    simpa using h
  have hprev := st214_p292
  have hstep := st214_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p294 : ((1651700259123/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT214 (i+1))
      = (∑ i ∈ Finset.range 293, stT214 (i+1)) + stT214 294 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 293
    simpa using h
  have hprev := st214_p293
  have hstep := st214_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p295 : ((1608039356353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT214 (i+1))
      = (∑ i ∈ Finset.range 294, stT214 (i+1)) + stT214 295 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 294
    simpa using h
  have hprev := st214_p294
  have hstep := st214_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p296 : ((1667230309321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT214 (i+1))
      = (∑ i ∈ Finset.range 295, stT214 (i+1)) + stT214 296 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 295
    simpa using h
  have hprev := st214_p295
  have hstep := st214_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p297 : ((3598231108863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT214 (i+1))
      = (∑ i ∈ Finset.range 296, stT214 (i+1)) + stT214 297 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 296
    simpa using h
  have hprev := st214_p296
  have hstep := st214_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p298 : ((3875774472881/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT214 (i+1))
      = (∑ i ∈ Finset.range 297, stT214 (i+1)) + stT214 298 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 297
    simpa using h
  have hprev := st214_p297
  have hstep := st214_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p299 : ((4030334094207/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT214 (i+1))
      = (∑ i ∈ Finset.range 298, stT214 (i+1)) + stT214 299 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 298
    simpa using h
  have hprev := st214_p298
  have hstep := st214_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p300 : ((7974059187553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT214 (i+1))
      = (∑ i ∈ Finset.range 299, stT214 (i+1)) + stT214 300 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 299
    simpa using h
  have hprev := st214_p299
  have hstep := st214_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p301 : ((3768105628743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT214 (i+1))
      = (∑ i ∈ Finset.range 300, stT214 (i+1)) + stT214 301 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 300
    simpa using h
  have hprev := st214_p300
  have hstep := st214_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p302 : ((3480373530561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT214 (i+1))
      = (∑ i ∈ Finset.range 301, stT214 (i+1)) + stT214 302 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 301
    simpa using h
  have hprev := st214_p301
  have hstep := st214_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p303 : ((6524720414427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT214 (i+1))
      = (∑ i ∈ Finset.range 302, stT214 (i+1)) + stT214 303 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 302
    simpa using h
  have hprev := st214_p302
  have hstep := st214_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p304 : ((6435259071687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT214 (i+1))
      = (∑ i ∈ Finset.range 303, stT214 (i+1)) + stT214 304 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 303
    simpa using h
  have hprev := st214_p303
  have hstep := st214_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p305 : ((6732665900289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT214 (i+1))
      = (∑ i ∈ Finset.range 304, stT214 (i+1)) + stT214 305 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 304
    simpa using h
  have hprev := st214_p304
  have hstep := st214_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p306 : ((3637269680281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT214 (i+1))
      = (∑ i ∈ Finset.range 305, stT214 (i+1)) + stT214 306 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 305
    simpa using h
  have hprev := st214_p305
  have hstep := st214_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p307 : ((3902882285711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT214 (i+1))
      = (∑ i ∈ Finset.range 306, stT214 (i+1)) + stT214 307 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 306
    simpa using h
  have hprev := st214_p306
  have hstep := st214_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p308 : ((4039645591949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT214 (i+1))
      = (∑ i ∈ Finset.range 307, stT214 (i+1)) + stT214 308 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 307
    simpa using h
  have hprev := st214_p307
  have hstep := st214_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p309 : ((7970190616837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT214 (i+1))
      = (∑ i ∈ Finset.range 308, stT214 (i+1)) + stT214 309 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 308
    simpa using h
  have hprev := st214_p308
  have hstep := st214_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p310 : ((7530837932117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT214 (i+1))
      = (∑ i ∈ Finset.range 309, stT214 (i+1)) + stT214 310 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 309
    simpa using h
  have hprev := st214_p309
  have hstep := st214_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p311 : ((6963763847909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT214 (i+1))
      = (∑ i ∈ Finset.range 310, stT214 (i+1)) + stT214 311 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 310
    simpa using h
  have hprev := st214_p310
  have hstep := st214_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p312 : ((6527022710027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT214 (i+1))
      = (∑ i ∈ Finset.range 311, stT214 (i+1)) + stT214 312 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 311
    simpa using h
  have hprev := st214_p311
  have hstep := st214_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p313 : ((1283358946397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT214 (i+1))
      = (∑ i ∈ Finset.range 312, stT214 (i+1)) + stT214 313 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 312
    simpa using h
  have hprev := st214_p312
  have hstep := st214_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p314 : ((6680560122793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT214 (i+1))
      = (∑ i ∈ Finset.range 313, stT214 (i+1)) + stT214 314 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 313
    simpa using h
  have hprev := st214_p313
  have hstep := st214_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p315 : ((7198621494841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT214 (i+1))
      = (∑ i ∈ Finset.range 314, stT214 (i+1)) + stT214 315 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 314
    simpa using h
  have hprev := st214_p314
  have hstep := st214_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p316 : ((3870048911017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT214 (i+1))
      = (∑ i ∈ Finset.range 315, stT214 (i+1)) + stT214 316 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 315
    simpa using h
  have hprev := st214_p315
  have hstep := st214_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p317 : ((8066553612579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT214 (i+1))
      = (∑ i ∈ Finset.range 316, stT214 (i+1)) + stT214 317 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 316
    simpa using h
  have hprev := st214_p316
  have hstep := st214_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p318 : ((1004553120201/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT214 (i+1))
      = (∑ i ∈ Finset.range 317, stT214 (i+1)) + stT214 318 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 317
    simpa using h
  have hprev := st214_p317
  have hstep := st214_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p319 : ((7664852532051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT214 (i+1))
      = (∑ i ∈ Finset.range 318, stT214 (i+1)) + stT214 319 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 318
    simpa using h
  have hprev := st214_p318
  have hstep := st214_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p320 : ((889298072379/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT214 (i+1))
      = (∑ i ∈ Finset.range 319, stT214 (i+1)) + stT214 320 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 319
    simpa using h
  have hprev := st214_p319
  have hstep := st214_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p321 : ((662249776513/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT214 (i+1))
      = (∑ i ∈ Finset.range 320, stT214 (i+1)) + stT214 321 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 320
    simpa using h
  have hprev := st214_p320
  have hstep := st214_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p322 : ((6398878978079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT214 (i+1))
      = (∑ i ∈ Finset.range 321, stT214 (i+1)) + stT214 322 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 321
    simpa using h
  have hprev := st214_p321
  have hstep := st214_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p323 : ((6536900252849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT214 (i+1))
      = (∑ i ∈ Finset.range 322, stT214 (i+1)) + stT214 323 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 322
    simpa using h
  have hprev := st214_p322
  have hstep := st214_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p324 : ((3488124073417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT214 (i+1))
      = (∑ i ∈ Finset.range 323, stT214 (i+1)) + stT214 324 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 323
    simpa using h
  have hprev := st214_p323
  have hstep := st214_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p325 : ((3765460205917/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT214 (i+1))
      = (∑ i ∈ Finset.range 324, stT214 (i+1)) + stT214 325 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 324
    simpa using h
  have hprev := st214_p324
  have hstep := st214_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p326 : ((3984492689869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT214 (i+1))
      = (∑ i ∈ Finset.range 325, stT214 (i+1)) + stT214 326 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 325
    simpa using h
  have hprev := st214_p325
  have hstep := st214_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p327 : ((2027379880967/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT214 (i+1))
      = (∑ i ∈ Finset.range 326, stT214 (i+1)) + stT214 327 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 326
    simpa using h
  have hprev := st214_p326
  have hstep := st214_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p328 : ((3948139432529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT214 (i+1))
      = (∑ i ∈ Finset.range 327, stT214 (i+1)) + stT214 328 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 327
    simpa using h
  have hprev := st214_p327
  have hstep := st214_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p329 : ((3709302961749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT214 (i+1))
      = (∑ i ∈ Finset.range 328, stT214 (i+1)) + stT214 329 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 328
    simpa using h
  have hprev := st214_p328
  have hstep := st214_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p330 : ((3436249577217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT214 (i+1))
      = (∑ i ∈ Finset.range 329, stT214 (i+1)) + stT214 330 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 329
    simpa using h
  have hprev := st214_p329
  have hstep := st214_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p331 : ((50620535153/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT214 (i+1))
      = (∑ i ∈ Finset.range 330, stT214 (i+1)) + stT214 331 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 330
    simpa using h
  have hprev := st214_p330
  have hstep := st214_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p332 : ((799592872133/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT214 (i+1))
      = (∑ i ∈ Finset.range 331, stT214 (i+1)) + stT214 332 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 331
    simpa using h
  have hprev := st214_p331
  have hstep := st214_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p333 : ((415986635389/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT214 (i+1))
      = (∑ i ∈ Finset.range 332, stT214 (i+1)) + stT214 333 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 332
    simpa using h
  have hprev := st214_p332
  have hstep := st214_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p334 : ((7151583075249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT214 (i+1))
      = (∑ i ∈ Finset.range 333, stT214 (i+1)) + stT214 334 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 333
    simpa using h
  have hprev := st214_p333
  have hstep := st214_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p335 : ((7686686646807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT214 (i+1))
      = (∑ i ∈ Finset.range 334, stT214 (i+1)) + stT214 335 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 334
    simpa using h
  have hprev := st214_p334
  have hstep := st214_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p336 : ((8050413924663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT214 (i+1))
      = (∑ i ∈ Finset.range 335, stT214 (i+1)) + stT214 336 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 335
    simpa using h
  have hprev := st214_p335
  have hstep := st214_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p337 : ((324058612227/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT214 (i+1))
      = (∑ i ∈ Finset.range 336, stT214 (i+1)) + stT214 337 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 336
    simpa using h
  have hprev := st214_p336
  have hstep := st214_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p338 : ((1955428071581/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT214 (i+1))
      = (∑ i ∈ Finset.range 337, stT214 (i+1)) + stT214 338 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 337
    simpa using h
  have hprev := st214_p337
  have hstep := st214_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p339 : ((3660549736987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT214 (i+1))
      = (∑ i ∈ Finset.range 338, stT214 (i+1)) + stT214 339 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 338
    simpa using h
  have hprev := st214_p338
  have hstep := st214_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p340 : ((1698316134017/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT214 (i+1))
      = (∑ i ∈ Finset.range 339, stT214 (i+1)) + stT214 340 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 339
    simpa using h
  have hprev := st214_p339
  have hstep := st214_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p341 : ((6440082891647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT214 (i+1))
      = (∑ i ∈ Finset.range 340, stT214 (i+1)) + stT214 341 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 340
    simpa using h
  have hprev := st214_p340
  have hstep := st214_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p342 : ((199838203019/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT214 (i+1))
      = (∑ i ∈ Finset.range 341, stT214 (i+1)) + stT214 342 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 341
    simpa using h
  have hprev := st214_p341
  have hstep := st214_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p343 : ((834112028951/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT214 (i+1))
      = (∑ i ∈ Finset.range 342, stT214 (i+1)) + stT214 343 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 342
    simpa using h
  have hprev := st214_p342
  have hstep := st214_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p344 : ((896005784699/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT214 (i+1))
      = (∑ i ∈ Finset.range 343, stT214 (i+1)) + stT214 344 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 343
    simpa using h
  have hprev := st214_p343
  have hstep := st214_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p345 : ((961758256229/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT214 (i+1))
      = (∑ i ∈ Finset.range 344, stT214 (i+1)) + stT214 345 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 344
    simpa using h
  have hprev := st214_p344
  have hstep := st214_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p346 : ((4027662794489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT214 (i+1))
      = (∑ i ∈ Finset.range 345, stT214 (i+1)) + stT214 346 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 345
    simpa using h
  have hprev := st214_p345
  have hstep := st214_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p347 : ((4059607549871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT214 (i+1))
      = (∑ i ∈ Finset.range 346, stT214 (i+1)) + stT214 347 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 346
    simpa using h
  have hprev := st214_p346
  have hstep := st214_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p348 : ((7863845585797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT214 (i+1))
      = (∑ i ∈ Finset.range 347, stT214 (i+1)) + stT214 348 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 347
    simpa using h
  have hprev := st214_p347
  have hstep := st214_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p349 : ((7384230214237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT214 (i+1))
      = (∑ i ∈ Finset.range 348, stT214 (i+1)) + stT214 349 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 348
    simpa using h
  have hprev := st214_p348
  have hstep := st214_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p350 : ((6855847814461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT214 (i+1))
      = (∑ i ∈ Finset.range 349, stT214 (i+1)) + stT214 350 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 349
    simpa using h
  have hprev := st214_p349
  have hstep := st214_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p351 : ((3234948222171/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT214 (i+1))
      = (∑ i ∈ Finset.range 350, stT214 (i+1)) + stT214 351 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 350
    simpa using h
  have hprev := st214_p350
  have hstep := st214_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p352 : ((318215410757/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT214 (i+1))
      = (∑ i ∈ Finset.range 351, stT214 (i+1)) + stT214 352 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 351
    simpa using h
  have hprev := st214_p351
  have hstep := st214_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p353 : ((205479059867/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT214 (i+1))
      = (∑ i ∈ Finset.range 352, stT214 (i+1)) + stT214 353 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 352
    simpa using h
  have hprev := st214_p352
  have hstep := st214_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p354 : ((3513133482323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT214 (i+1))
      = (∑ i ∈ Finset.range 353, stT214 (i+1)) + stT214 354 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 353
    simpa using h
  have hprev := st214_p353
  have hstep := st214_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p355 : ((3778211980891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT214 (i+1))
      = (∑ i ∈ Finset.range 354, stT214 (i+1)) + stT214 355 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 354
    simpa using h
  have hprev := st214_p354
  have hstep := st214_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p356 : ((1994744264309/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT214 (i+1))
      = (∑ i ∈ Finset.range 355, stT214 (i+1)) + stT214 356 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 355
    simpa using h
  have hprev := st214_p355
  have hstep := st214_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p357 : ((2036682774377/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT214 (i+1))
      = (∑ i ∈ Finset.range 356, stT214 (i+1)) + stT214 357 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 356
    simpa using h
  have hprev := st214_p356
  have hstep := st214_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p358 : ((4001333438307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT214 (i+1))
      = (∑ i ∈ Finset.range 357, stT214 (i+1)) + stT214 358 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 357
    simpa using h
  have hprev := st214_p357
  have hstep := st214_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p359 : ((3799119545217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT214 (i+1))
      = (∑ i ∈ Finset.range 358, stT214 (i+1)) + stT214 359 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 358
    simpa using h
  have hprev := st214_p358
  have hstep := st214_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p360 : ((3536967421511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT214 (i+1))
      = (∑ i ∈ Finset.range 359, stT214 (i+1)) + stT214 360 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 359
    simpa using h
  have hprev := st214_p359
  have hstep := st214_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p361 : ((3304892328681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT214 (i+1))
      = (∑ i ∈ Finset.range 360, stT214 (i+1)) + stT214 361 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 360
    simpa using h
  have hprev := st214_p360
  have hstep := st214_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p362 : ((795430793619/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT214 (i+1))
      = (∑ i ∈ Finset.range 361, stT214 (i+1)) + stT214 362 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 361
    simpa using h
  have hprev := st214_p361
  have hstep := st214_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p363 : ((100268301963/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT214 (i+1))
      = (∑ i ∈ Finset.range 362, stT214 (i+1)) + stT214 363 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 362
    simpa using h
  have hprev := st214_p362
  have hstep := st214_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p364 : ((843913457187/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT214 (i+1))
      = (∑ i ∈ Finset.range 363, stT214 (i+1)) + stT214 364 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 363
    simpa using h
  have hprev := st214_p363
  have hstep := st214_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p365 : ((7252489890803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT214 (i+1))
      = (∑ i ∈ Finset.range 364, stT214 (i+1)) + stT214 365 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 364
    simpa using h
  have hprev := st214_p364
  have hstep := st214_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p366 : ((7752876691079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT214 (i+1))
      = (∑ i ∈ Finset.range 365, stT214 (i+1)) + stT214 366 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 365
    simpa using h
  have hprev := st214_p365
  have hstep := st214_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p367 : ((8086638206099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT214 (i+1))
      = (∑ i ∈ Finset.range 366, stT214 (i+1)) + stT214 367 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 366
    simpa using h
  have hprev := st214_p366
  have hstep := st214_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p368 : ((1628919060973/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT214 (i+1))
      = (∑ i ∈ Finset.range 367, stT214 (i+1)) + stT214 368 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 367
    simpa using h
  have hprev := st214_p367
  have hstep := st214_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p369 : ((1581828955913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT214 (i+1))
      = (∑ i ∈ Finset.range 368, stT214 (i+1)) + stT214 369 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 368
    simpa using h
  have hprev := st214_p368
  have hstep := st214_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p370 : ((7458570329869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT214 (i+1))
      = (∑ i ∈ Finset.range 369, stT214 (i+1)) + stT214 370 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 369
    simpa using h
  have hprev := st214_p369
  have hstep := st214_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p371 : ((3470080556497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT214 (i+1))
      = (∑ i ∈ Finset.range 370, stT214 (i+1)) + stT214 371 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 370
    simpa using h
  have hprev := st214_p370
  have hstep := st214_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p372 : ((3260790978909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT214 (i+1))
      = (∑ i ∈ Finset.range 371, stT214 (i+1)) + stT214 372 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 371
    simpa using h
  have hprev := st214_p371
  have hstep := st214_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p373 : ((6336726374103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT214 (i+1))
      = (∑ i ∈ Finset.range 372, stT214 (i+1)) + stT214 373 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 372
    simpa using h
  have hprev := st214_p372
  have hstep := st214_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p374 : ((6443442789163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT214 (i+1))
      = (∑ i ∈ Finset.range 373, stT214 (i+1)) + stT214 374 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 373
    simpa using h
  have hprev := st214_p373
  have hstep := st214_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p375 : ((340317839461/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT214 (i+1))
      = (∑ i ∈ Finset.range 374, stT214 (i+1)) + stT214 375 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 374
    simpa using h
  have hprev := st214_p374
  have hstep := st214_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p376 : ((91367988927/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT214 (i+1))
      = (∑ i ∈ Finset.range 375, stT214 (i+1)) + stT214 376 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 375
    simpa using h
  have hprev := st214_p375
  have hstep := st214_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p377 : ((779376698943/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT214 (i+1))
      = (∑ i ∈ Finset.range 376, stT214 (i+1)) + stT214 377 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 376
    simpa using h
  have hprev := st214_p376
  have hstep := st214_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p378 : ((4053947178963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT214 (i+1))
      = (∑ i ∈ Finset.range 377, stT214 (i+1)) + stT214 378 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 377
    simpa using h
  have hprev := st214_p377
  have hstep := st214_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p379 : ((8154875699821/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT214 (i+1))
      = (∑ i ∈ Finset.range 378, stT214 (i+1)) + stT214 379 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 378
    simpa using h
  have hprev := st214_p378
  have hstep := st214_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p380 : ((7921495516231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT214 (i+1))
      = (∑ i ∈ Finset.range 379, stT214 (i+1)) + stT214 380 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 379
    simpa using h
  have hprev := st214_p379
  have hstep := st214_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p381 : ((7481036958391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT214 (i+1))
      = (∑ i ∈ Finset.range 380, stT214 (i+1)) + stT214 381 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 380
    simpa using h
  have hprev := st214_p380
  have hstep := st214_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p382 : ((6969523962801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT214 (i+1))
      = (∑ i ∈ Finset.range 381, stT214 (i+1)) + stT214 382 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 381
    simpa using h
  have hprev := st214_p381
  have hstep := st214_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p383 : ((1635822230353/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT214 (i+1))
      = (∑ i ∈ Finset.range 382, stT214 (i+1)) + stT214 383 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 382
    simpa using h
  have hprev := st214_p382
  have hstep := st214_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p384 : ((6331232757539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT214 (i+1))
      = (∑ i ∈ Finset.range 383, stT214 (i+1)) + stT214 384 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 383
    simpa using h
  have hprev := st214_p383
  have hstep := st214_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p385 : ((6396307544381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT214 (i+1))
      = (∑ i ∈ Finset.range 384, stT214 (i+1)) + stT214 385 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 384
    simpa using h
  have hprev := st214_p384
  have hstep := st214_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p386 : ((6717594777161/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT214 (i+1))
      = (∑ i ∈ Finset.range 385, stT214 (i+1)) + stT214 386 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 385
    simpa using h
  have hprev := st214_p385
  have hstep := st214_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p387 : ((7197820880337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT214 (i+1))
      = (∑ i ∈ Finset.range 386, stT214 (i+1)) + stT214 387 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 386
    simpa using h
  have hprev := st214_p386
  have hstep := st214_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p388 : ((3846706900651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT214 (i+1))
      = (∑ i ∈ Finset.range 387, stT214 (i+1)) + stT214 388 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 387
    simpa using h
  have hprev := st214_p387
  have hstep := st214_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p389 : ((4028834061871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT214 (i+1))
      = (∑ i ∈ Finset.range 388, stT214 (i+1)) + stT214 389 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 388
    simpa using h
  have hprev := st214_p388
  have hstep := st214_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p390 : ((8183989466327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT214 (i+1))
      = (∑ i ∈ Finset.range 389, stT214 (i+1)) + stT214 390 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 389
    simpa using h
  have hprev := st214_p389
  have hstep := st214_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p391 : ((1607305602247/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT214 (i+1))
      = (∑ i ∈ Finset.range 390, stT214 (i+1)) + stT214 391 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 390
    simpa using h
  have hprev := st214_p390
  have hstep := st214_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p392 : ((7659574903979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT214 (i+1))
      = (∑ i ∈ Finset.range 391, stT214 (i+1)) + stT214 392 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 391
    simpa using h
  have hprev := st214_p391
  have hstep := st214_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p393 : ((286541972573/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT214 (i+1))
      = (∑ i ∈ Finset.range 392, stT214 (i+1)) + stT214 393 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 392
    simpa using h
  have hprev := st214_p392
  have hstep := st214_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p394 : ((6692154234569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT214 (i+1))
      = (∑ i ∈ Finset.range 393, stT214 (i+1)) + stT214 394 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 393
    simpa using h
  have hprev := st214_p393
  have hstep := st214_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p395 : ((3190307121877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT214 (i+1))
      = (∑ i ∈ Finset.range 394, stT214 (i+1)) + stT214 395 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 394
    simpa using h
  have hprev := st214_p394
  have hstep := st214_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p396 : ((3158588122597/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT214 (i+1))
      = (∑ i ∈ Finset.range 395, stT214 (i+1)) + stT214 396 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 395
    simpa using h
  have hprev := st214_p395
  have hstep := st214_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p397 : ((6518670525569/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT214 (i+1))
      = (∑ i ∈ Finset.range 396, stT214 (i+1)) + stT214 397 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 396
    simpa using h
  have hprev := st214_p396
  have hstep := st214_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p398 : ((6926828123911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT214 (i+1))
      = (∑ i ∈ Finset.range 397, stT214 (i+1)) + stT214 398 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 397
    simpa using h
  have hprev := st214_p397
  have hstep := st214_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p399 : ((7425737977983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT214 (i+1))
      = (∑ i ∈ Finset.range 398, stT214 (i+1)) + stT214 399 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 398
    simpa using h
  have hprev := st214_p398
  have hstep := st214_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p400 : ((7875185477983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT214 (i+1))
      = (∑ i ∈ Finset.range 399, stT214 (i+1)) + stT214 400 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 399
    simpa using h
  have hprev := st214_p399
  have hstep := st214_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p401 : ((8150089968479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT214 (i+1))
      = (∑ i ∈ Finset.range 400, stT214 (i+1)) + stT214 401 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 400
    simpa using h
  have hprev := st214_p400
  have hstep := st214_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p402 : ((1635001443913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT214 (i+1))
      = (∑ i ∈ Finset.range 401, stT214 (i+1)) + stT214 402 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 401
    simpa using h
  have hprev := st214_p401
  have hstep := st214_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p403 : ((1588844660289/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT214 (i+1))
      = (∑ i ∈ Finset.range 402, stT214 (i+1)) + stT214 403 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 402
    simpa using h
  have hprev := st214_p402
  have hstep := st214_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p404 : ((3761176281457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT214 (i+1))
      = (∑ i ∈ Finset.range 403, stT214 (i+1)) + stT214 404 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 403
    simpa using h
  have hprev := st214_p403
  have hstep := st214_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p405 : ((3512821674641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT214 (i+1))
      = (∑ i ∈ Finset.range 404, stT214 (i+1)) + stT214 405 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 404
    simpa using h
  have hprev := st214_p404
  have hstep := st214_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p406 : ((658960814617/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT214 (i+1))
      = (∑ i ∈ Finset.range 405, stT214 (i+1)) + stT214 406 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 405
    simpa using h
  have hprev := st214_p405
  have hstep := st214_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p407 : ((633204186533/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT214 (i+1))
      = (∑ i ∈ Finset.range 406, stT214 (i+1)) + stT214 407 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 406
    simpa using h
  have hprev := st214_p406
  have hstep := st214_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p408 : ((632152649357/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT214 (i+1))
      = (∑ i ∈ Finset.range 407, stT214 (i+1)) + stT214 408 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 407
    simpa using h
  have hprev := st214_p407
  have hstep := st214_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p409 : ((3279862292669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT214 (i+1))
      = (∑ i ∈ Finset.range 408, stT214 (i+1)) + stT214 409 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 408
    simpa using h
  have hprev := st214_p408
  have hstep := st214_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p410 : ((698188101413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT214 (i+1))
      = (∑ i ∈ Finset.range 409, stT214 (i+1)) + stT214 410 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 409
    simpa using h
  have hprev := st214_p409
  have hstep := st214_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p411 : ((7474974824921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT214 (i+1))
      = (∑ i ∈ Finset.range 410, stT214 (i+1)) + stT214 411 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 410
    simpa using h
  have hprev := st214_p410
  have hstep := st214_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p412 : ((7908282666201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT214 (i+1))
      = (∑ i ∈ Finset.range 411, stT214 (i+1)) + stT214 412 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 411
    simpa using h
  have hprev := st214_p411
  have hstep := st214_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p413 : ((4084021187583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT214 (i+1))
      = (∑ i ∈ Finset.range 412, stT214 (i+1)) + stT214 413 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 412
    simpa using h
  have hprev := st214_p412
  have hstep := st214_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p414 : ((2046751096613/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT214 (i+1))
      = (∑ i ∈ Finset.range 413, stT214 (i+1)) + stT214 414 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 413
    simpa using h
  have hprev := st214_p413
  have hstep := st214_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p415 : ((497582676779/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT214 (i+1))
      = (∑ i ∈ Finset.range 414, stT214 (i+1)) + stT214 415 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 414
    simpa using h
  have hprev := st214_p414
  have hstep := st214_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p416 : ((1510136018341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT214 (i+1))
      = (∑ i ∈ Finset.range 415, stT214 (i+1)) + stT214 416 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 415
    simpa using h
  have hprev := st214_p415
  have hstep := st214_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p417 : ((7061964332953/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT214 (i+1))
      = (∑ i ∈ Finset.range 416, stT214 (i+1)) + stT214 417 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 416
    simpa using h
  have hprev := st214_p416
  have hstep := st214_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p418 : ((6621151472649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT214 (i+1))
      = (∑ i ∈ Finset.range 417, stT214 (i+1)) + stT214 418 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 417
    simpa using h
  have hprev := st214_p417
  have hstep := st214_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p419 : ((6340797125277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT214 (i+1))
      = (∑ i ∈ Finset.range 418, stT214 (i+1)) + stT214 419 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 418
    simpa using h
  have hprev := st214_p418
  have hstep := st214_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p420 : ((3145779238909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT214 (i+1))
      = (∑ i ∈ Finset.range 419, stT214 (i+1)) + stT214 420 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 419
    simpa using h
  have hprev := st214_p419
  have hstep := st214_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p421 : ((1621214426277/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT214 (i+1))
      = (∑ i ∈ Finset.range 420, stT214 (i+1)) + stT214 421 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 420
    simpa using h
  have hprev := st214_p420
  have hstep := st214_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p422 : ((1717705971423/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT214 (i+1))
      = (∑ i ∈ Finset.range 421, stT214 (i+1)) + stT214 422 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 421
    simpa using h
  have hprev := st214_p421
  have hstep := st214_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p423 : ((1837912423779/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT214 (i+1))
      = (∑ i ∈ Finset.range 422, stT214 (i+1)) + stT214 423 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 422
    simpa using h
  have hprev := st214_p422
  have hstep := st214_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p424 : ((487919547559/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT214 (i+1))
      = (∑ i ∈ Finset.range 423, stT214 (i+1)) + stT214 424 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 423
    simpa using h
  have hprev := st214_p423
  have hstep := st214_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p425 : ((4061448295437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT214 (i+1))
      = (∑ i ∈ Finset.range 424, stT214 (i+1)) + stT214 425 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 424
    simpa using h
  have hprev := st214_p424
  have hstep := st214_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p426 : ((1644501127193/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT214 (i+1))
      = (∑ i ∈ Finset.range 425, stT214 (i+1)) + stT214 426 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 425
    simpa using h
  have hprev := st214_p425
  have hstep := st214_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p427 : ((8081946037797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT214 (i+1))
      = (∑ i ∈ Finset.range 426, stT214 (i+1)) + stT214 427 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 426
    simpa using h
  have hprev := st214_p426
  have hstep := st214_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p428 : ((7736789636181/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT214 (i+1))
      = (∑ i ∈ Finset.range 427, stT214 (i+1)) + stT214 428 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 427
    simpa using h
  have hprev := st214_p427
  have hstep := st214_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p429 : ((3636126264483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT214 (i+1))
      = (∑ i ∈ Finset.range 428, stT214 (i+1)) + stT214 429 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 428
    simpa using h
  have hprev := st214_p428
  have hstep := st214_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p430 : ((6801831716111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT214 (i+1))
      = (∑ i ∈ Finset.range 429, stT214 (i+1)) + stT214 430 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 429
    simpa using h
  have hprev := st214_p429
  have hstep := st214_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p431 : ((6439416527983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT214 (i+1))
      = (∑ i ∈ Finset.range 430, stT214 (i+1)) + stT214 431 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 430
    simpa using h
  have hprev := st214_p430
  have hstep := st214_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p432 : ((1254371628769/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT214 (i+1))
      = (∑ i ∈ Finset.range 431, stT214 (i+1)) + stT214 432 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 431
    simpa using h
  have hprev := st214_p431
  have hstep := st214_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p433 : ((6338488074557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT214 (i+1))
      = (∑ i ∈ Finset.range 432, stT214 (i+1)) + stT214 433 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 432
    simpa using h
  have hprev := st214_p432
  have hstep := st214_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p434 : ((6622347824897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT214 (i+1))
      = (∑ i ∈ Finset.range 433, stT214 (i+1)) + stT214 434 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 433
    simpa using h
  have hprev := st214_p433
  have hstep := st214_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p435 : ((1763748654797/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT214 (i+1))
      = (∑ i ∈ Finset.range 434, stT214 (i+1)) + stT214 435 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 434
    simpa using h
  have hprev := st214_p434
  have hstep := st214_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p436 : ((1883344724809/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT214 (i+1))
      = (∑ i ∈ Finset.range 435, stT214 (i+1)) + stT214 436 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 435
    simpa using h
  have hprev := st214_p435
  have hstep := st214_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p437 : ((1986148018593/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT214 (i+1))
      = (∑ i ∈ Finset.range 436, stT214 (i+1)) + stT214 437 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 436
    simpa using h
  have hprev := st214_p436
  have hstep := st214_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p438 : ((1024058714779/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT214 (i+1))
      = (∑ i ∈ Finset.range 437, stT214 (i+1)) + stT214 438 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 437
    simpa using h
  have hprev := st214_p437
  have hstep := st214_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p439 : ((1643969314957/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT214 (i+1))
      = (∑ i ∈ Finset.range 438, stT214 (i+1)) + stT214 439 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 438
    simpa using h
  have hprev := st214_p438
  have hstep := st214_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p440 : ((8021315823973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT214 (i+1))
      = (∑ i ∈ Finset.range 439, stT214 (i+1)) + stT214 440 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 439
    simpa using h
  have hprev := st214_p439
  have hstep := st214_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p441 : ((477737599949/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT214 (i+1))
      = (∑ i ∈ Finset.range 440, stT214 (i+1)) + stT214 441 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 440
    simpa using h
  have hprev := st214_p440
  have hstep := st214_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p442 : ((358752399007/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT214 (i+1))
      = (∑ i ∈ Finset.range 441, stT214 (i+1)) + stT214 442 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 441
    simpa using h
  have hprev := st214_p441
  have hstep := st214_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p443 : ((42018529093/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT214 (i+1))
      = (∑ i ∈ Finset.range 442, stT214 (i+1)) + stT214 443 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 442
    simpa using h
  have hprev := st214_p442
  have hstep := st214_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p444 : ((6390713320717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT214 (i+1))
      = (∑ i ∈ Finset.range 443, stT214 (i+1)) + stT214 444 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 443
    simpa using h
  have hprev := st214_p443
  have hstep := st214_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p445 : ((6253306347157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT214 (i+1))
      = (∑ i ∈ Finset.range 444, stT214 (i+1)) + stT214 445 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 444
    simpa using h
  have hprev := st214_p444
  have hstep := st214_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p446 : ((31705030817/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT214 (i+1))
      = (∑ i ∈ Finset.range 445, stT214 (i+1)) + stT214 446 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 445
    simpa using h
  have hprev := st214_p445
  have hstep := st214_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p447 : ((6633068909053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT214 (i+1))
      = (∑ i ∈ Finset.range 446, stT214 (i+1)) + stT214 447 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 446
    simpa using h
  have hprev := st214_p446
  have hstep := st214_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p448 : ((3531543764249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT214 (i+1))
      = (∑ i ∈ Finset.range 447, stT214 (i+1)) + stT214 448 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 447
    simpa using h
  have hprev := st214_p447
  have hstep := st214_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p449 : ((7534398773437/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT214 (i+1))
      = (∑ i ∈ Finset.range 448, stT214 (i+1)) + stT214 449 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 448
    simpa using h
  have hprev := st214_p448
  have hstep := st214_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p450 : ((7941993999401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT214 (i+1))
      = (∑ i ∈ Finset.range 449, stT214 (i+1)) + stT214 450 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 449
    simpa using h
  have hprev := st214_p449
  have hstep := st214_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p451 : ((51224210803/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT214 (i+1))
      = (∑ i ∈ Finset.range 450, stT214 (i+1)) + stT214 451 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 450
    simpa using h
  have hprev := st214_p450
  have hstep := st214_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p452 : ((206017887477/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT214 (i+1))
      = (∑ i ∈ Finset.range 451, stT214 (i+1)) + stT214 452 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 451
    simpa using h
  have hprev := st214_p451
  have hstep := st214_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p453 : ((2016887255189/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT214 (i+1))
      = (∑ i ∈ Finset.range 452, stT214 (i+1)) + stT214 453 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 452
    simpa using h
  have hprev := st214_p452
  have hstep := st214_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p454 : ((120549292949/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT214 (i+1))
      = (∑ i ∈ Finset.range 453, stT214 (i+1)) + stT214 454 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 453
    simpa using h
  have hprev := st214_p453
  have hstep := st214_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p455 : ((907621636191/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT214 (i+1))
      = (∑ i ∈ Finset.range 454, stT214 (i+1)) + stT214 455 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 454
    simpa using h
  have hprev := st214_p454
  have hstep := st214_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p456 : ((3401929121719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT214 (i+1))
      = (∑ i ∈ Finset.range 455, stT214 (i+1)) + stT214 456 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 455
    simpa using h
  have hprev := st214_p455
  have hstep := st214_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p457 : ((3221222514733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT214 (i+1))
      = (∑ i ∈ Finset.range 456, stT214 (i+1)) + stT214 457 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 456
    simpa using h
  have hprev := st214_p456
  have hstep := st214_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p458 : ((3126989108373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT214 (i+1))
      = (∑ i ∈ Finset.range 457, stT214 (i+1)) + stT214 458 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 457
    simpa using h
  have hprev := st214_p457
  have hstep := st214_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p459 : ((3139026382013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT214 (i+1))
      = (∑ i ∈ Finset.range 458, stT214 (i+1)) + stT214 459 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 458
    simpa using h
  have hprev := st214_p458
  have hstep := st214_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p460 : ((3254315348423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT214 (i+1))
      = (∑ i ∈ Finset.range 459, stT214 (i+1)) + stT214 460 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 459
    simpa using h
  have hprev := st214_p459
  have hstep := st214_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p461 : ((689594693343/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT214 (i+1))
      = (∑ i ∈ Finset.range 460, stT214 (i+1)) + stT214 461 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 460
    simpa using h
  have hprev := st214_p460
  have hstep := st214_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p462 : ((91969180719/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT214 (i+1))
      = (∑ i ∈ Finset.range 461, stT214 (i+1)) + stT214 462 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 461
    simpa using h
  have hprev := st214_p461
  have hstep := st214_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p463 : ((7796003156067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT214 (i+1))
      = (∑ i ∈ Finset.range 462, stT214 (i+1)) + stT214 463 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 462
    simpa using h
  have hprev := st214_p462
  have hstep := st214_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p464 : ((324784771509/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT214 (i+1))
      = (∑ i ∈ Finset.range 463, stT214 (i+1)) + stT214 464 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 463
    simpa using h
  have hprev := st214_p463
  have hstep := st214_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p465 : ((8261364053591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT214 (i+1))
      = (∑ i ∈ Finset.range 464, stT214 (i+1)) + stT214 465 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 464
    simpa using h
  have hprev := st214_p464
  have hstep := st214_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p466 : ((1638511465921/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT214 (i+1))
      = (∑ i ∈ Finset.range 465, stT214 (i+1)) + stT214 466 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 465
    simpa using h
  have hprev := st214_p465
  have hstep := st214_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p467 : ((792829152677/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT214 (i+1))
      = (∑ i ∈ Finset.range 466, stT214 (i+1)) + stT214 467 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 466
    simpa using h
  have hprev := st214_p466
  have hstep := st214_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p468 : ((940472768523/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT214 (i+1))
      = (∑ i ∈ Finset.range 467, stT214 (i+1)) + stT214 468 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 467
    simpa using h
  have hprev := st214_p467
  have hstep := st214_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p469 : ((1765636021923/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT214 (i+1))
      = (∑ i ∈ Finset.range 468, stT214 (i+1)) + stT214 469 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 468
    simpa using h
  have hprev := st214_p468
  have hstep := st214_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p470 : ((207468388383/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT214 (i+1))
      = (∑ i ∈ Finset.range 469, stT214 (i+1)) + stT214 470 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 469
    simpa using h
  have hprev := st214_p469
  have hstep := st214_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p471 : ((158477067309/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT214 (i+1))
      = (∑ i ∈ Finset.range 470, stT214 (i+1)) + stT214 471 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 470
    simpa using h
  have hprev := st214_p470
  have hstep := st214_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p472 : ((6223046389/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT214 (i+1))
      = (∑ i ∈ Finset.range 471, stT214 (i+1)) + stT214 472 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 471
    simpa using h
  have hprev := st214_p471
  have hstep := st214_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p473 : ((1972975817/3125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT214 (i+1))
      = (∑ i ∈ Finset.range 472, stT214 (i+1)) + stT214 473 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 472
    simpa using h
  have hprev := st214_p472
  have hstep := st214_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p474 : ((329575094483/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT214 (i+1))
      = (∑ i ∈ Finset.range 473, stT214 (i+1)) + stT214 474 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 473
    simpa using h
  have hprev := st214_p473
  have hstep := st214_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p475 : ((7000619009641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT214 (i+1))
      = (∑ i ∈ Finset.range 474, stT214 (i+1)) + stT214 475 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 474
    simpa using h
  have hprev := st214_p474
  have hstep := st214_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p476 : ((3729428315417/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT214 (i+1))
      = (∑ i ∈ Finset.range 475, stT214 (i+1)) + stT214 476 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 475
    simpa using h
  have hprev := st214_p475
  have hstep := st214_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p477 : ((3937563890451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT214 (i+1))
      = (∑ i ∈ Finset.range 476, stT214 (i+1)) + stT214 477 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 476
    simpa using h
  have hprev := st214_p476
  have hstep := st214_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p478 : ((1633474107279/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT214 (i+1))
      = (∑ i ∈ Finset.range 477, stT214 (i+1)) + stT214 478 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 477
    simpa using h
  have hprev := st214_p477
  have hstep := st214_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p479 : ((4139300703573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT214 (i+1))
      = (∑ i ∈ Finset.range 478, stT214 (i+1)) + stT214 479 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 478
    simpa using h
  have hprev := st214_p478
  have hstep := st214_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p480 : ((4093869802749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT214 (i+1))
      = (∑ i ∈ Finset.range 479, stT214 (i+1)) + stT214 480 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 479
    simpa using h
  have hprev := st214_p479
  have hstep := st214_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p481 : ((3956667490161/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT214 (i+1))
      = (∑ i ∈ Finset.range 480, stT214 (i+1)) + stT214 481 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 480
    simpa using h
  have hprev := st214_p480
  have hstep := st214_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p482 : ((750942917437/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT214 (i+1))
      = (∑ i ∈ Finset.range 481, stT214 (i+1)) + stT214 482 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 481
    simpa using h
  have hprev := st214_p481
  have hstep := st214_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p483 : ((3527351964797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT214 (i+1))
      = (∑ i ∈ Finset.range 482, stT214 (i+1)) + stT214 483 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 482
    simpa using h
  have hprev := st214_p482
  have hstep := st214_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p484 : ((663699706471/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT214 (i+1))
      = (∑ i ∈ Finset.range 483, stT214 (i+1)) + stT214 484 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 483
    simpa using h
  have hprev := st214_p483
  have hstep := st214_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p485 : ((3168164535503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT214 (i+1))
      = (∑ i ∈ Finset.range 484, stT214 (i+1)) + stT214 485 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 484
    simpa using h
  have hprev := st214_p484
  have hstep := st214_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p486 : ((1552429702159/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT214 (i+1))
      = (∑ i ∈ Finset.range 485, stT214 (i+1)) + stT214 486 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 485
    simpa using h
  have hprev := st214_p485
  have hstep := st214_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p487 : ((1570143062029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT214 (i+1))
      = (∑ i ∈ Finset.range 486, stT214 (i+1)) + stT214 487 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 486
    simpa using h
  have hprev := st214_p486
  have hstep := st214_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p488 : ((51052083961/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT214 (i+1))
      = (∑ i ∈ Finset.range 487, stT214 (i+1)) + stT214 488 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 487
    simpa using h
  have hprev := st214_p487
  have hstep := st214_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p489 : ((1730819200707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT214 (i+1))
      = (∑ i ∈ Finset.range 488, stT214 (i+1)) + stT214 489 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 488
    simpa using h
  have hprev := st214_p488
  have hstep := st214_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p490 : ((7372771489581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT214 (i+1))
      = (∑ i ∈ Finset.range 489, stT214 (i+1)) + stT214 490 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 489
    simpa using h
  have hprev := st214_p489
  have hstep := st214_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p491 : ((7798690089363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT214 (i+1))
      = (∑ i ∈ Finset.range 490, stT214 (i+1)) + stT214 491 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 490
    simpa using h
  have hprev := st214_p490
  have hstep := st214_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p492 : ((8121640066089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT214 (i+1))
      = (∑ i ∈ Finset.range 491, stT214 (i+1)) + stT214 492 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 491
    simpa using h
  have hprev := st214_p491
  have hstep := st214_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p493 : ((8282004002971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT214 (i+1))
      = (∑ i ∈ Finset.range 492, stT214 (i+1)) + stT214 493 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 492
    simpa using h
  have hprev := st214_p492
  have hstep := st214_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p494 : ((8250718226779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT214 (i+1))
      = (∑ i ∈ Finset.range 493, stT214 (i+1)) + stT214 494 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 493
    simpa using h
  have hprev := st214_p493
  have hstep := st214_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p495 : ((8034306158817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT214 (i+1))
      = (∑ i ∈ Finset.range 494, stT214 (i+1)) + stT214 495 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 494
    simpa using h
  have hprev := st214_p494
  have hstep := st214_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p496 : ((7673224366493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT214 (i+1))
      = (∑ i ∈ Finset.range 495, stT214 (i+1)) + stT214 496 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 495
    simpa using h
  have hprev := st214_p495
  have hstep := st214_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p497 : ((7234086654113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT214 (i+1))
      = (∑ i ∈ Finset.range 496, stT214 (i+1)) + stT214 497 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 496
    simpa using h
  have hprev := st214_p496
  have hstep := st214_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p498 : ((3398601537609/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT214 (i+1))
      = (∑ i ∈ Finset.range 497, stT214 (i+1)) + stT214 498 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 497
    simpa using h
  have hprev := st214_p497
  have hstep := st214_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p499 : ((322092247533/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT214 (i+1))
      = (∑ i ∈ Finset.range 498, stT214 (i+1)) + stT214 499 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 498
    simpa using h
  have hprev := st214_p498
  have hstep := st214_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_p500 : ((1557982463621/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT214 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT214 (i+1))
      = (∑ i ∈ Finset.range 499, stT214 (i+1)) + stT214 500 := by
    have h := Finset.sum_range_succ (fun i => stT214 (i+1)) 499
    simpa using h
  have hprev := st214_p499
  have hstep := st214_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st214_s500 :
    |Real.sin (((214 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))
      - ((-883021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -5148331/10000000) (δ := 2681/250000000) (ψ := -4983/100000) 214 212
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 214`** (evaluated boundary). -/
theorem station_214_sign : 0 < hardyG ((((214:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 214 500 (by norm_num) (by norm_num)
    ((-4983/100000 : ℚ) : ℝ)
  have hchain := st214_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT214 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((214 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-4983/100000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st214_c500
  have hsinb := abs_le.mp st214_s500
  have hbdy_lo : ((21152105613717/228981250000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((214 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-4983/100000 : ℚ) : ℝ))) / 2
          - ((((214:ℕ)):ℝ))
            * Real.sin (((214 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((-4983/100000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((214:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((214:ℝ) * Real.log (500:ℝ) - ((-4983/100000 : ℚ) : ℝ))) / 2
        - ((214:ℝ)) * Real.sin ((214:ℝ) * Real.log (500:ℝ) - ((-4983/100000 : ℚ) : ℝ))
        ≥ ((47297609/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((214:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((47297609/250000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (447213/10000000)
          * ((47297609/250000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((47297609/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((214:ℕ)):ℝ))+1) * (((((214:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((92385691727/250000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1557982463621/2500000000000 : ℚ) : ℝ) + ((21152105613717/228981250000000 : ℚ) : ℝ)
      - ((92385691727/250000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-4983/100000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((214:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-4983/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((214:ℕ)):ℝ)))).re
      - Real.sin ((-4983/100000 : ℚ) : ℝ)
        * (riemannZeta (line ((((214:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((214:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((214:ℕ)):ℝ))
      = (((((214:ℕ)):ℝ)) * (Real.log ((((214:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((214:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_214
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
  have hθwin : |(((-4983/100000 : ℚ) : ℝ) + ((43:ℤ)) * (2*Real.pi)) - theta ((((214:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((214:ℕ)):ℝ)))
    (φ := ((-4983/100000 : ℚ) : ℝ) + ((43:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-4983/100000 : ℚ)) : ℝ) 43).1,
    (cos_sin_shift (((-4983/100000 : ℚ)) : ℝ) 43).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_214_sign
end AxiomAudit
