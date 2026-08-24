import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 323` (rung-335.5; evaluated boundary, N = 500)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT323 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((323 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((3441/250000 : ℚ) : ℝ))

theorem st323_c1 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((199981/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3441/1000000) (δ := 1/1000000000) (ψ := 3441/250000) 323 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t1 : ((199961/200000 : ℚ) : ℝ) ≤ stT323 1 := by
  have hc : ((199961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199961/200000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((199961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c2 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-13649/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1451191/2500000) (δ := 101/6250000) (ψ := 3441/250000) 323 36
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t2 : ((-24131787317/50000000000 : ℚ) : ℝ) ≤ stT323 2 := by
  have hc : ((-13651/20000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24131787317/50000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-13651/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c3 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-98691/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7449039/10000000) (δ := 4051/250000000) (ψ := 3441/250000) 323 56
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t3 : ((-569850519603/1000000000000 : ℚ) : ℝ) ≤ stT323 3 := by
  have hc : ((-98701/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-569850519603/1000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-98701/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c4 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-16453/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2066443/5000000) (δ := 16311/1000000000) (ψ := 3441/250000) 323 71
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t4 : ((-82365016473/2000000000000 : ℚ) : ℝ) ≤ stT323 4 := by
  have hc : ((-16473/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82365016473/2000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-16473/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c5 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-98729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4174217/10000000) (δ := 8153/500000000) (ψ := 3441/250000) 323 83
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t5 : ((-55247091093/1250000000000 : ℚ) : ℝ) ≤ stT323 5 := by
  have hc : ((-98829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55247091093/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-98829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c6 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((48931/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67149/400000) (δ := 16241/1000000000) (ψ := 3441/250000) 323 92
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t6 : ((399468822459/1250000000000 : ℚ) : ℝ) ≤ stT323 6 := by
  have hc : ((195699/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399468822459/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((195699/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c7 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((12259/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 491709/10000000) (δ := 4071/250000000) (ψ := 3441/250000) 323 100
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t7 : ((46329931241/125000000000 : ℚ) : ℝ) ≤ stT323 7 := by
  have hc : ((49031/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46329931241/125000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((49031/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c8 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((158613/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -409357/2500000) (δ := 1617/100000000) (ψ := 3441/250000) 323 107
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t8 : ((560710785069/2000000000000 : ℚ) : ℝ) ≤ stT323 8 := by
  have hc : ((158593/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((560710785069/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((158593/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c9 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((23807/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155087/2000000) (δ := 16213/1000000000) (ψ := 3441/250000) 323 113
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t9 : ((158696650797/500000000000 : ℚ) : ℝ) ≤ stT323 9 := by
  have hc : ((47609/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158696650797/500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((47609/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c10 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-670249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720419/1250000) (δ := 8127/500000000) (ψ := 3441/250000) 323 118
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t10 : ((-1059914947511/5000000000000 : ℚ) : ℝ) ≤ stT323 10 := by
  have hc : ((-670349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1059914947511/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-670349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c11 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-51813/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2093261/5000000) (δ := 8159/500000000) (ψ := 3441/250000) 323 123
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t11 : ((-78186428691/2500000000000 : ℚ) : ℝ) ≤ stT323 11 := by
  have hc : ((-51863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78186428691/2500000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-51863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c12 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-65791/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1022897/2500000) (δ := 51/3125000) (ψ := 3441/250000) 323 128
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t12 : ((-5944093001/312500000000 : ℚ) : ℝ) ≤ stT323 12 := by
  have hc : ((-65891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5944093001/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-65891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c13 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((609327/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2288961/10000000) (δ := 16249/1000000000) (ψ := 3441/250000) 323 132
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t13 : ((3379382169/20000000000 : ℚ) : ℝ) ≤ stT323 13 := by
  have hc : ((609227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3379382169/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((609227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c14 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-514689/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1319651/2500000) (δ := 8139/500000000) (ψ := 3441/250000) 323 136
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t14 : ((-1375831773657/10000000000000 : ℚ) : ℝ) ≤ stT323 14 := by
  have hc : ((-514789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1375831773657/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-514789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c15 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((244581/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3309273/10000000) (δ := 16299/1000000000) (ψ := 3441/250000) 323 139
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t15 : ((157811752057/2500000000000 : ℚ) : ℝ) ≤ stT323 15 := by
  have hc : ((244481/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157811752057/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((244481/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c16 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-61507/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3703871/5000000) (δ := 651/40000000) (ψ := 3441/250000) 323 143
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t16 : ((-615132746053/2500000000000 : ℚ) : ℝ) ≤ stT323 16 := by
  have hc : ((-246053/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-615132746053/2500000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-246053/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c17 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-153301/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5577267/10000000) (δ := 16153/1000000000) (ψ := 3441/250000) 323 146
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t17 : ((-185935143691/1250000000000 : ℚ) : ℝ) ≤ stT323 17 := by
  have hc : ((-76663/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-185935143691/1250000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-76663/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c18 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-433089/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6545749/10000000) (δ := 2029/125000000) (ψ := 3441/250000) 323 149
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t18 : ((-1020918585197/5000000000000 : ℚ) : ℝ) ≤ stT323 18 := by
  have hc : ((-433139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1020918585197/5000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-433139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c19 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-650497/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5697589/10000000) (δ := 8143/500000000) (ψ := 3441/250000) 323 151
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t19 : ((-746286156163/5000000000000 : ℚ) : ℝ) ≤ stT323 19 := by
  have hc : ((-650597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-746286156163/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-650597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c20 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((249999/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6961/10000000) (δ := 16307/1000000000) (ψ := 3441/250000) 323 154
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t20 : ((279479306129/1250000000000 : ℚ) : ℝ) ≤ stT323 20 := by
  have hc : ((124987/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((279479306129/1250000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((124987/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c21 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-39953/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1546553/2000000) (δ := 8137/500000000) (ψ := 3441/250000) 323 157
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t21 : ((-87193326303/400000000000 : ℚ) : ℝ) ≤ stT323 21 := by
  have hc : ((-39957/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87193326303/400000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-39957/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c22 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((805951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1583791/10000000) (δ := 16243/1000000000) (ψ := 3441/250000) 323 159
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t22 : ((1718079972957/10000000000000 : ℚ) : ℝ) ≤ stT323 22 := by
  have hc : ((805851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1718079972957/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((805851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c23 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((100283/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2895111/10000000) (δ := 16257/1000000000) (ψ := 3441/250000) 323 161
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t23 : ((13065772947/156250000000 : ℚ) : ℝ) ≤ stT323 23 := by
  have hc : ((50129/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13065772947/156250000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((50129/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c24 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-69443/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5846061/10000000) (δ := 16231/1000000000) (ψ := 3441/250000) 323 163
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t24 : ((-70885190313/500000000000 : ℚ) : ℝ) ≤ stT323 24 := by
  have hc : ((-69453/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70885190313/500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-69453/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c25 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-491557/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 73939/100000) (δ := 8143/500000000) (ψ := 3441/250000) 323 165
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t25 : ((-983214491607/5000000000000 : ℚ) : ℝ) ≤ stT323 25 := by
  have hc : ((-491607/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-983214491607/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-491607/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c26 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-99663/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 478043/625000) (δ := 16303/1000000000) (ψ := 3441/250000) 323 167
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t26 : ((-97737450013/500000000000 : ℚ) : ℝ) ≤ stT323 26 := by
  have hc : ((-99673/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97737450013/500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-99673/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c27 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-448387/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3354027/5000000) (δ := 4047/250000000) (ψ := 3441/250000) 323 169
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t27 : ((-863017454937/5000000000000 : ℚ) : ℝ) ≤ stT323 27 := by
  have hc : ((-448437/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-863017454937/5000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-448437/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c28 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-57731/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 931809/2000000) (δ := 8137/500000000) (ψ := 3441/250000) 323 171
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t28 : ((-109139168073/2000000000000 : ℚ) : ℝ) ≤ stT323 28 := by
  have hc : ((-57751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109139168073/2000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-57751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c29 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((807003/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98709/625000) (δ := 2043/125000000) (ψ := 3441/250000) 323 173
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t29 : ((1498380946559/10000000000000 : ℚ) : ℝ) ≤ stT323 29 := by
  have hc : ((806903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1498380946559/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((806903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c30 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((276661/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1230561/5000000) (δ := 3249/200000000) (ψ := 3441/250000) 323 175
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t30 : ((505020043751/5000000000000 : ℚ) : ℝ) ≤ stT323 30 := by
  have hc : ((276611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((505020043751/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((276611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c31 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-1967/2000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1849801/2500000) (δ := 4043/250000000) (ψ := 3441/250000) 323 177
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t31 : ((-2208248393/12500000000 : ℚ) : ℝ) ≤ stT323 31 := by
  have hc : ((-2459/2500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2208248393/12500000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-2459/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c32 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((530197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 632477/2500000) (δ := 16179/1000000000) (ψ := 3441/250000) 323 178
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t32 : ((468543726651/5000000000000 : ℚ) : ℝ) ≤ stT323 32 := by
  have hc : ((530097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((468543726651/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((530097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c33 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-4437/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63093/156250) (δ := 16309/1000000000) (ψ := 3441/250000) 323 180
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t33 : ((-7741235319/1000000000000 : ℚ) : ℝ) ≤ stT323 33 := by
  have hc : ((-4447/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7741235319/1000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-4447/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c34 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-17249/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4360383/10000000) (δ := 16301/1000000000) (ψ := 3441/250000) 323 181
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t34 : ((-14799471687/500000000000 : ℚ) : ℝ) ≤ stT323 34 := by
  have hc : ((-17259/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14799471687/500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-17259/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c35 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((11131/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1824069/5000000) (δ := 509/31250000) (ψ := 3441/250000) 323 183
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t35 : ((4699478817/250000000000 : ℚ) : ℝ) ≤ stT323 35 := by
  have hc : ((11121/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4699478817/250000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((11121/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c36 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((42481/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3391901/10000000) (δ := 16223/1000000000) (ψ := 3441/250000) 323 184
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t36 : ((35384152513/1000000000000 : ℚ) : ℝ) ≤ stT323 36 := by
  have hc : ((42461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35384152513/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((42461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c37 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-141921/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5899333/10000000) (δ := 16237/1000000000) (ψ := 3441/250000) 323 186
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t37 : ((-23334958459/200000000000 : ℚ) : ℝ) ≤ stT323 37 := by
  have hc : ((-141941/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23334958459/200000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-141941/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c38 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((999577/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2909/400000) (δ := 16159/1000000000) (ψ := 3441/250000) 323 187
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t38 : ((810682791039/5000000000000 : ℚ) : ℝ) ≤ stT323 38 := by
  have hc : ((999477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((810682791039/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((999477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c39 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-48557/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 162329/312500) (δ := 2019/125000000) (ψ := 3441/250000) 323 188
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t39 : ((-38884731447/500000000000 : ℚ) : ℝ) ≤ stT323 39 := by
  have hc : ((-48567/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38884731447/500000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-48567/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c40 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-168593/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231091/400000) (δ := 8083/500000000) (ψ := 3441/250000) 323 190
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t40 : ((-133304247951/1250000000000 : ℚ) : ℝ) ≤ stT323 40 := by
  have hc : ((-84309/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-133304247951/1250000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-84309/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c41 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((162963/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -386491/2500000) (δ := 1623/100000000) (ψ := 3441/250000) 323 191
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t41 : ((254474111991/2000000000000 : ℚ) : ℝ) ≤ stT323 41 := by
  have hc : ((162943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254474111991/2000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((162943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c42 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((158911/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 440977/2000000) (δ := 809/50000000) (ψ := 3441/250000) 323 192
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t42 : ((122583170619/1250000000000 : ℚ) : ℝ) ≤ stT323 42 := by
  have hc : ((79443/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122583170619/1250000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((79443/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c43 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-587789/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27489/50000) (δ := 4079/250000000) (ψ := 3441/250000) 323 193
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t43 : ((-448261247277/5000000000000 : ℚ) : ℝ) ≤ stT323 43 := by
  have hc : ((-587889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448261247277/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-587889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c44 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-245019/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1470821/2000000) (δ := 16201/1000000000) (ψ := 3441/250000) 323 195
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t44 : ((-92354449377/625000000000 : ℚ) : ℝ) ≤ stT323 44 := by
  have hc : ((-61261/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92354449377/625000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-61261/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c45 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-3851/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2457641/5000000) (δ := 16209/1000000000) (ψ := 3441/250000) 323 196
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t45 : ((-179444457/3125000000 : ℚ) : ℝ) ≤ stT323 45 := by
  have hc : ((-963/2500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-179444457/3125000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-963/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c46 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((6381/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -718821/2500000) (δ := 16287/1000000000) (ψ := 3441/250000) 323 197
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t46 : ((150495421749/2500000000000 : ℚ) : ℝ) ≤ stT323 46 := by
  have hc : ((102071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150495421749/2500000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((102071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c47 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((883851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -121691/1000000) (δ := 407/25000000) (ψ := 3441/250000) 323 198
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t47 : ((1289082512399/10000000000000 : ℚ) : ℝ) ≤ stT323 47 := by
  have hc : ((883751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1289082512399/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((883751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c48 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((999541/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18937/2500000) (δ := 1633/100000000) (ψ := 3441/250000) 323 199
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t48 : ((11540545227/80000000000 : ℚ) : ℝ) ≤ stT323 48 := by
  have hc : ((999441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11540545227/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((999441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c49 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((918267/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 254447/2500000) (δ := 8133/500000000) (ψ := 3441/250000) 323 200
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t49 : ((1311666749357/10000000000000 : ℚ) : ℝ) ≤ stT323 49 := by
  have hc : ((918167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1311666749357/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((918167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c50 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((398213/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811793/5000000) (δ := 8079/500000000) (ψ := 3441/250000) 323 201
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t50 : ((563087290719/5000000000000 : ℚ) : ℝ) ≤ stT323 50 := by
  have hc : ((398163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((563087290719/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((398163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c51 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((723119/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 953111/5000000) (δ := 16251/1000000000) (ψ := 3441/250000) 323 202
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t51 : ((25310726133/250000000000 : ℚ) : ℝ) ≤ stT323 51 := by
  have hc : ((723019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25310726133/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((723019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c52 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((45673/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15027/80000) (δ := 16259/1000000000) (ψ := 3441/250000) 323 203
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t52 : ((1013253849/10000000000 : ℚ) : ℝ) ≤ stT323 52 := by
  have hc : ((182667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1013253849/10000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((182667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c53 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((203363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1551833/10000000) (δ := 8083/500000000) (ψ := 3441/250000) 323 204
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t53 : ((27930609349/250000000000 : ℚ) : ℝ) ≤ stT323 53 := by
  have hc : ((101669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27930609349/250000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((101669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c54 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((116309/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46887/500000) (δ := 1633/100000000) (ψ := 3441/250000) 323 205
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t54 : ((316518834411/2500000000000 : ℚ) : ℝ) ≤ stT323 54 := by
  have hc : ((232593/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316518834411/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((232593/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c55 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((499913/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1867/400000) (δ := 16323/1000000000) (ψ := 3441/250000) 323 206
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t55 : ((674014769337/5000000000000 : ℚ) : ℝ) ≤ stT323 55 := by
  have hc : ((499863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((674014769337/5000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((499863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c56 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((902809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1111349/10000000) (δ := 4047/250000000) (ψ := 3441/250000) 323 207
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t56 : ((603147726477/5000000000000 : ℚ) : ℝ) ≤ stT323 56 := by
  have hc : ((902709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((603147726477/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((902709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c57 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((265611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -505377/2000000) (δ := 3259/200000000) (ψ := 3441/250000) 323 208
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t57 : ((87936010613/1250000000000 : ℚ) : ℝ) ≤ stT323 57 := by
  have hc : ((265561/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87936010613/1250000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((265561/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c58 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-26349/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -419097/1000000) (δ := 8101/500000000) (ψ := 3441/250000) 323 209
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t58 : ((-3463077631/250000000000 : ℚ) : ℝ) ≤ stT323 58 := by
  have hc : ((-13187/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3463077631/250000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-13187/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c59 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-47661/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1219041/2000000) (δ := 16309/1000000000) (ψ := 3441/250000) 323 210
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t59 : ((-24823006441/250000000000 : ℚ) : ℝ) ≤ stT323 59 := by
  have hc : ((-190669/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24823006441/250000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-190669/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c60 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-61789/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467283/625000) (δ := 16209/1000000000) (ψ := 3441/250000) 323 210
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t60 : ((-63821887019/500000000000 : ℚ) : ℝ) ≤ stT323 60 := by
  have hc : ((-247181/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63821887019/500000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-247181/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c61 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-228933/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2557987/5000000) (δ := 16287/1000000000) (ψ := 3441/250000) 323 211
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t61 : ((-293182734727/5000000000000 : ℚ) : ℝ) ≤ stT323 61 := by
  have hc : ((-228983/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293182734727/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-228983/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c62 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((263663/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 507673/2000000) (δ := 507/31250000) (ψ := 3441/250000) 323 212
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t62 : ((334788773613/5000000000000 : ℚ) : ℝ) ≤ stT323 62 := by
  have hc : ((263613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334788773613/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((263613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c63 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((995033/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9971/400000) (δ := 16331/1000000000) (ψ := 3441/250000) 323 213
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t63 : ((1253497182973/10000000000000 : ℚ) : ℝ) ≤ stT323 63 := by
  have hc : ((994933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1253497182973/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((994933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c64 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((67791/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1620243/5000000) (δ := 8169/500000000) (ψ := 3441/250000) 323 214
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t64 : ((33883/1000000 : ℚ) : ℝ) ≤ stT323 64 := by
  have hc : ((33883/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33883/1000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((33883/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c65 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-841863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -803601/1250000) (δ := 3249/200000000) (ψ := 3441/250000) 323 215
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t65 : ((-261081780781/2500000000000 : ℚ) : ℝ) ≤ stT323 65 := by
  have hc : ((-841963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261081780781/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-841963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c66 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-709707/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2949849/5000000) (δ := 8079/500000000) (ψ := 3441/250000) 323 215
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t66 : ((-174742416681/2000000000000 : ℚ) : ℝ) ≤ stT323 66 := by
  have hc : ((-709807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-174742416681/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-709807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c67 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((23787/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2334839/10000000) (δ := 2019/125000000) (ψ := 3441/250000) 323 216
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t67 : ((14527774201/200000000000 : ℚ) : ℝ) ≤ stT323 67 := by
  have hc : ((23783/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14527774201/200000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((23783/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c68 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((422569/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1409931/10000000) (δ := 16159/1000000000) (ψ := 3441/250000) 323 217
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t68 : ((256189747941/2500000000000 : ℚ) : ℝ) ≤ stT323 68 := by
  have hc : ((422519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((256189747941/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((422519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c69 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-53199/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5329363/10000000) (δ := 16267/1000000000) (ψ := 3441/250000) 323 218
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t69 : ((-64056133531/1000000000000 : ℚ) : ℝ) ≤ stT323 69 := by
  have hc : ((-53209/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64056133531/1000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-53209/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c70 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-405251/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 786189/1250000) (δ := 16167/1000000000) (ψ := 3441/250000) 323 218
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t70 : ((-484427508929/5000000000000 : ℚ) : ℝ) ≤ stT323 70 := by
  have hc : ((-405301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484427508929/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-405301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c71 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((686417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2035613/10000000) (δ := 16229/1000000000) (ψ := 3441/250000) 323 219
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t71 : ((814507975577/10000000000000 : ℚ) : ℝ) ≤ stT323 71 := by
  have hc : ((686317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((814507975577/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((686317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c72 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((145143/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2378413/10000000) (δ := 8111/500000000) (ψ := 3441/250000) 323 220
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t72 : ((85511579649/1250000000000 : ℚ) : ℝ) ≤ stT323 72 := by
  have hc : ((72559/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85511579649/1250000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((72559/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c73 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-233773/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3474143/5000000) (δ := 509/31250000) (ψ := 3441/250000) 323 221
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t73 : ((-34204998097/312500000000 : ℚ) : ℝ) ≤ stT323 73 := by
  have hc : ((-116899/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34204998097/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-116899/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c74 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-44483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1009559/2500000) (δ := 509/31250000) (ψ := 3441/250000) 323 221
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t74 : ((-51826712091/10000000000000 : ℚ) : ℝ) ≤ stT323 74 := by
  have hc : ((-44583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51826712091/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-44583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c75 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((472659/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -415287/5000000) (δ := 3259/200000000) (ψ := 3441/250000) 323 222
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t75 : ((5457216123/50000000000 : ℚ) : ℝ) ≤ stT323 75 := by
  have hc : ((472609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5457216123/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((472609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c76 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-17339/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5843039/10000000) (δ := 163/10000000) (ψ := 3441/250000) 323 223
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t76 : ((-39784140957/500000000000 : ℚ) : ℝ) ≤ stT323 76 := by
  have hc : ((-34683/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39784140957/500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-34683/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c77 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-38641/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2356341/5000000) (δ := 81/5000000) (ψ := 3441/250000) 323 223
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t77 : ((-44049760521/1250000000000 : ℚ) : ℝ) ≤ stT323 77 := by
  have hc : ((-77307/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44049760521/1250000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-77307/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c78 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((194719/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287893/5000000) (δ := 16293/1000000000) (ψ := 3441/250000) 323 224
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t78 : ((220453199623/2000000000000 : ℚ) : ℝ) ≤ stT323 78 := by
  have hc : ((194699/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((220453199623/2000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((194699/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c79 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-92073/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2998503/5000000) (δ := 16317/1000000000) (ψ := 3441/250000) 323 225
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t79 : ((-6475268189/78125000000 : ℚ) : ℝ) ≤ stT323 79 := by
  have hc : ((-184171/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6475268189/78125000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-184171/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c80 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-46609/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33283/80000) (δ := 16317/1000000000) (ψ := 3441/250000) 323 225
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t80 : ((-26083174203/2500000000000 : ℚ) : ℝ) ≤ stT323 80 := by
  have hc : ((-46659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26083174203/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-46659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c81 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((821609/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -75821/500000) (δ := 16179/1000000000) (ψ := 3441/250000) 323 226
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t81 : ((912787686499/10000000000000 : ℚ) : ℝ) ≤ stT323 81 := by
  have hc : ((821509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((912787686499/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((821509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c82 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-976959/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7316277/10000000) (δ := 16331/1000000000) (ψ := 3441/250000) 323 227
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t82 : ((-269745471661/2500000000000 : ℚ) : ℝ) ≤ stT323 82 := by
  have hc : ((-977059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269745471661/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-977059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c83 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((21991/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2471753/10000000) (δ := 4043/250000000) (ψ := 3441/250000) 323 227
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t83 : ((12066927327/200000000000 : ℚ) : ℝ) ≤ stT323 83 := by
  have hc : ((21987/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12066927327/200000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((21987/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c84 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((28821/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3565469/10000000) (δ := 16169/500000000) (ψ := 3441/250000) 323 228
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t84 : ((31424454289/2000000000000 : ℚ) : ℝ) ≤ stT323 84 := by
  have hc : ((28801/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31424454289/2000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((28801/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c85 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-183729/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5990849/10000000) (δ := 3253/200000000) (ψ := 3441/250000) 323 228
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t85 : ((-99654663681/1250000000000 : ℚ) : ℝ) ≤ stT323 85 := by
  have hc : ((-91877/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99654663681/1250000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-91877/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c86 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((994061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -136297/5000000) (δ := 16157/1000000000) (ψ := 3441/250000) 323 229
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t86 : ((1071814983247/10000000000000 : ℚ) : ℝ) ≤ stT323 86 := by
  have hc : ((993961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1071814983247/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((993961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c87 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-177071/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6645131/10000000) (δ := 327/20000000) (ψ := 3441/250000) 323 230
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t87 : ((-189861563283/2000000000000 : ℚ) : ℝ) ≤ stT323 87 := by
  have hc : ((-177091/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-189861563283/2000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-177091/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c88 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((255943/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 516709/2000000) (δ := 16253/1000000000) (ψ := 3441/250000) 323 230
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t88 : ((272782705679/5000000000000 : ℚ) : ℝ) ≤ stT323 88 := by
  have hc : ((255893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((272782705679/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((255893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c89 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-7307/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -500009/1250000) (δ := 813/50000000) (ψ := 3441/250000) 323 231
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t89 : ((-971488167/312500000000 : ℚ) : ℝ) ≤ stT323 89 := by
  have hc : ((-1833/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-971488167/312500000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-1833/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c90 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-84853/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5022367/10000000) (δ := 16343/1000000000) (ψ := 3441/250000) 323 231
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t90 : ((-89464035189/2000000000000 : ℚ) : ℝ) ≤ stT323 90 := by
  have hc : ((-84873/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89464035189/2000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-84873/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c91 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((761523/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -881421/5000000) (δ := 2021/62500000) (ψ := 3441/250000) 323 232
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t91 : ((199546887033/2500000000000 : ℚ) : ℝ) ≤ stT323 91 := by
  have hc : ((761423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199546887033/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((761423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c92 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-190057/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3531183/5000000) (δ := 16167/1000000000) (ψ := 3441/250000) 323 232
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t92 : ((-198169148121/2000000000000 : ℚ) : ℝ) ≤ stT323 92 := by
  have hc : ((-190077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-198169148121/2000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-190077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c93 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((999433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 21051/2500000) (δ := 16329/1000000000) (ψ := 3441/250000) 323 233
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t93 : ((1036259353683/10000000000000 : ℚ) : ℝ) ≤ stT323 93 := by
  have hc : ((999333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1036259353683/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((999333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c94 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-940509/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -873413/1250000) (δ := 8091/500000000) (ψ := 3441/250000) 323 234
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t94 : ((-485082407999/5000000000000 : ℚ) : ℝ) ≤ stT323 94 := by
  have hc : ((-940609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485082407999/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-940609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c95 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((32483/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778871/5000000) (δ := 8141/500000000) (ψ := 3441/250000) 323 234
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t95 : ((16661369731/200000000000 : ℚ) : ℝ) ≤ stT323 95 := by
  have hc : ((32479/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16661369731/200000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((32479/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c96 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-649603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5694647/10000000) (δ := 8107/500000000) (ψ := 3441/250000) 323 235
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t96 : ((-663100525563/10000000000000 : ℚ) : ℝ) ≤ stT323 96 := by
  have hc : ((-649703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-663100525563/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-649703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c97 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((120179/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1336657/5000000) (δ := 8107/500000000) (ψ := 3441/250000) 323 235
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t97 : ((30499470821/625000000000 : ℚ) : ℝ) ≤ stT323 97 := by
  have hc : ((60077/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30499470821/625000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((60077/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c98 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-64849/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -190101/400000) (δ := 2037/125000000) (ψ := 3441/250000) 323 236
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t98 : ((-65527614957/2000000000000 : ℚ) : ℝ) ≤ stT323 98 := by
  have hc : ((-64869/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65527614957/2000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-64869/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c99 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((191393/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1722769/5000000) (δ := 2037/125000000) (ψ := 3441/250000) 323 236
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t99 : ((192256542841/10000000000000 : ℚ) : ℝ) ≤ stT323 99 := by
  have hc : ((191293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192256542841/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((191293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c100 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-43907/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -518351/1250000) (δ := 16303/1000000000) (ψ := 3441/250000) 323 237
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t100 : ((-43957/5000000 : ℚ) : ℝ) ≤ stT323 100 := by
  have hc : ((-43957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-43957/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-43957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c101 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((777/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194407/500000) (δ := 16303/1000000000) (ψ := 3441/250000) 323 237
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t101 : ((192042141/125000000000 : ℚ) : ℝ) ≤ stT323 101 := by
  have hc : ((193/12500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192042141/125000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((193/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c102 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((25157/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3864091/10000000) (δ := 1631/100000000) (ψ := 3441/250000) 323 238
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t102 : ((24810113379/10000000000000 : ℚ) : ℝ) ≤ stT323 102 := by
  have hc : ((25057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24810113379/10000000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((25057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c103 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-1739/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4013959/10000000) (δ := 16293/1000000000) (ψ := 3441/250000) 323 238
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t103 : ((-10740097/3125000000 : ℚ) : ℝ) ≤ stT323 103 := by
  have hc : ((-109/3125 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10740097/3125000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-109/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c104 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((3497/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -194601/500000) (δ := 8143/500000000) (ψ := 3441/250000) 323 239
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t104 : ((10639293/7812500000 : ℚ) : ℝ) ≤ stT323 104 := by
  have hc : ((217/15625 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10639293/7812500000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((217/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c105 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((36647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 479419/1250000) (δ := 16317/1000000000) (ψ := 3441/250000) 323 239
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t105 : ((356662173/100000000000 : ℚ) : ℝ) ≤ stT323 105 := by
  have hc : ((36547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356662173/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((36547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c106 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-29091/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4218561/10000000) (δ := 653/40000000) (ψ := 3441/250000) 323 240
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t106 : ((-3534995397/312500000000 : ℚ) : ℝ) ≤ stT323 106 := by
  have hc : ((-7279/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3534995397/312500000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-7279/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c107 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((111707/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1681851/5000000) (δ := 8089/500000000) (ψ := 3441/250000) 323 240
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t107 : ((6746427597/312500000000 : ℚ) : ℝ) ≤ stT323 107 := by
  have hc : ((111657/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6746427597/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((111657/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c108 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-354363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4832573/10000000) (δ := 2029/125000000) (ψ := 3441/250000) 323 241
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t108 : ((-341082376213/10000000000000 : ℚ) : ℝ) ≤ stT323 108 := by
  have hc : ((-354463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341082376213/10000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-354463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c109 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((20113/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2609831/10000000) (δ := 16271/1000000000) (ψ := 3441/250000) 323 241
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t109 : ((9630461517/200000000000 : ℚ) : ℝ) ≤ stT323 109 := by
  have hc : ((20109/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9630461517/200000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((20109/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c110 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-82297/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2861819/5000000) (δ := 16239/1000000000) (ψ := 3441/250000) 323 242
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t110 : ((-156958125597/2500000000000 : ℚ) : ℝ) ≤ stT323 110 := by
  have hc : ((-164619/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156958125597/2500000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-164619/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c111 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((100733/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 396039/2500000) (δ := 4041/250000000) (ψ := 3441/250000) 323 242
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t111 : ((191199135237/2500000000000 : ℚ) : ℝ) ≤ stT323 111 := by
  have hc : ((201441/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191199135237/2500000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((201441/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c112 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-231329/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6881663/10000000) (δ := 16257/1000000000) (ψ := 3441/250000) 323 243
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t112 : ((-6831536589/78125000000 : ℚ) : ℝ) ≤ stT323 112 := by
  have hc : ((-115677/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6831536589/78125000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-115677/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c113 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((992989/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 59241/2000000) (δ := 8123/500000000) (ψ := 3441/250000) 323 243
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t113 : ((11675381751/125000000000 : ℚ) : ℝ) ≤ stT323 113 := by
  have hc : ((992889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11675381751/125000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((992889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c114 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-492163/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1852691/2500000) (δ := 16257/1000000000) (ψ := 3441/250000) 323 243
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t114 : ((-230499902409/2500000000000 : ℚ) : ℝ) ≤ stT323 114 := by
  have hc : ((-492213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230499902409/2500000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-492213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c115 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((87859/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19449/156250) (δ := 16253/1000000000) (ψ := 3441/250000) 323 244
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t115 : ((10239942987/125000000000 : ℚ) : ℝ) ≤ stT323 115 := by
  have hc : ((87849/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10239942987/125000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((87849/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c116 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-665261/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5746599/10000000) (δ := 16253/1000000000) (ψ := 3441/250000) 323 244
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t116 : ((-617772385197/10000000000000 : ℚ) : ℝ) ≤ stT323 116 := by
  have hc : ((-665361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-617772385197/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-665361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c117 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((5487/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1514973/5000000) (δ := 101/6250000) (ψ := 3441/250000) 323 245
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t117 : ((162281183/5000000000 : ℚ) : ℝ) ≤ stT323 117 := by
  have hc : ((87767/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162281183/5000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((87767/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c118 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((8453/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 960611/2500000) (δ := 16243/1000000000) (ψ := 3441/250000) 323 245
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t118 : ((969824709/312500000000 : ℚ) : ℝ) ≤ stT323 118 := by
  have hc : ((2107/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((969824709/312500000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((2107/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c119 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-108669/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1262797/2500000) (δ := 2021/125000000) (ψ := 3441/250000) 323 246
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t119 : ((-49819840553/1250000000000 : ℚ) : ℝ) ≤ stT323 119 := by
  have hc : ((-54347/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).2
  have h0 : (0:ℝ) ≤ ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49819840553/1250000000000 : ℚ) : ℝ)
      = ((916699/10000000 : ℚ) : ℝ) * ((-54347/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c120 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((776007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 853107/5000000) (δ := 3247/200000000) (ψ := 3441/250000) 323 246
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t120 : ((70830222309/1000000000000 : ℚ) : ℝ) ≤ stT323 120 := by
  have hc : ((775907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70830222309/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((775907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c121 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-97559/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1825117/2500000) (δ := 647/40000000) (ψ := 3441/250000) 323 247
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t121 : ((-88699099779/1000000000000 : ℚ) : ℝ) ≤ stT323 121 := by
  have hc : ((-97569/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88699099779/1000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-97569/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c122 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((482971/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -654339/10000000) (δ := 651/40000000) (ψ := 3441/250000) 323 247
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t122 : ((437215907797/5000000000000 : ℚ) : ℝ) ≤ stT323 122 := by
  have hc : ((482921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437215907797/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((482921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c123 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-144057/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 237501/400000) (δ := 2041/125000000) (ψ := 3441/250000) 323 247
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t123 : ((-12990990859/200000000000 : ℚ) : ℝ) ≤ stT323 123 := by
  have hc : ((-144077/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12990990859/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-144077/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c124 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((274449/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3231949/10000000) (δ := 16221/1000000000) (ψ := 3441/250000) 323 248
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t124 : ((123186267537/5000000000000 : ℚ) : ℝ) ≤ stT323 124 := by
  have hc : ((274349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123186267537/5000000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((274349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c125 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((16621/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3254053/10000000) (δ := 8141/500000000) (ψ := 3441/250000) 323 248
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t125 : ((59442723993/2500000000000 : ℚ) : ℝ) ≤ stT323 125 := by
  have hc : ((66459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59442723993/2500000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((66459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c126 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-92833/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6019589/10000000) (δ := 16189/1000000000) (ψ := 3441/250000) 323 249
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t126 : ((-165426726861/2500000000000 : ℚ) : ℝ) ≤ stT323 126 := by
  have hc : ((-185691/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165426726861/2500000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-185691/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c127 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((123679/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363779/10000000) (δ := 8107/500000000) (ψ := 3441/250000) 323 249
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t127 : ((54868105387/625000000000 : ℚ) : ℝ) ≤ stT323 127 := by
  have hc : ((247333/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54868105387/625000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((247333/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c128 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-447419/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6697163/10000000) (δ := 8107/500000000) (ψ := 3441/250000) 323 249
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t128 : ((-98877672399/1250000000000 : ℚ) : ℝ) ≤ stT323 128 := by
  have hc : ((-447469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98877672399/1250000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-447469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c129 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((115473/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1363337/5000000) (δ := 16307/1000000000) (ψ := 3441/250000) 323 250
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t129 : ((254115479/6250000000 : ℚ) : ℝ) ≤ stT323 129 := by
  have hc : ((14431/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((254115479/6250000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((14431/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c130 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((166481/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3508841/10000000) (δ := 16307/1000000000) (ψ := 3441/250000) 323 250
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t130 : ((72962893549/5000000000000 : ℚ) : ℝ) ≤ stT323 130 := by
  have hc : ((166381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72962893549/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((166381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c131 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-740447/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601133/1000000) (δ := 4051/250000000) (ψ := 3441/250000) 323 251
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t131 : ((-129403923327/2000000000000 : ℚ) : ℝ) ≤ stT323 131 := by
  have hc : ((-740547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129403923327/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-740547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c132 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((998661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16173/1250000) (δ := 16299/1000000000) (ψ := 3441/250000) 323 251
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t132 : ((217283877917/2500000000000 : ℚ) : ℝ) ≤ stT323 132 := by
  have hc : ((998561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((217283877917/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((998561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c133 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-158963/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1555937/2500000) (δ := 16299/1000000000) (ψ := 3441/250000) 323 251
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t133 : ((-13785574913/200000000000 : ℚ) : ℝ) ≤ stT323 133 := by
  have hc : ((-158983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13785574913/200000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-158983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c134 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((97663/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -687103/2000000) (δ := 32311/1000000000) (ψ := 3441/250000) 323 252
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t134 : ((21081186771/1250000000000 : ℚ) : ℝ) ≤ stT323 134 := by
  have hc : ((97613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21081186771/1250000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((97613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c135 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((258573/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2568207/10000000) (δ := 253/15625000) (ψ := 3441/250000) 323 252
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t135 : ((111250461113/2500000000000 : ℚ) : ℝ) ≤ stT323 135 := by
  have hc : ((258523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111250461113/2500000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((258523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c136 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-481957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287213/400000) (δ := 8159/500000000) (ψ := 3441/250000) 323 253
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t136 : ((-413317628451/5000000000000 : ℚ) : ℝ) ≤ stT323 136 := by
  have hc : ((-482007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-413317628451/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-482007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c137 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((874787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2529/20000) (δ := 3257/200000000) (ψ := 3441/250000) 323 253
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t137 : ((747294961259/10000000000000 : ℚ) : ℝ) ≤ stT323 137 := by
  have hc : ((874687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((747294961259/10000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((874687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c138 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-269127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2304103/5000000) (δ := 8159/500000000) (ψ := 3441/250000) 323 253
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t138 : ((-229181368339/10000000000000 : ℚ) : ℝ) ≤ stT323 138 := by
  have hc : ((-269227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-229181368339/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-269227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c139 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-511517/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053873/2000000) (δ := 653/40000000) (ψ := 3441/250000) 323 254
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t139 : ((-433947911613/10000000000000 : ℚ) : ℝ) ≤ stT323 139 := by
  have hc : ((-511617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-433947911613/10000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-511617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c140 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((61157/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 259599/5000000) (δ := 8139/500000000) (ψ := 3441/250000) 323 254
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t140 : ((103363601931/1250000000000 : ℚ) : ℝ) ≤ stT323 140 := by
  have hc : ((244603/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((103363601931/1250000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((244603/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c141 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-201269/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6266499/10000000) (δ := 649/40000000) (ψ := 3441/250000) 323 254
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t141 : ((-10595009043/156250000000 : ℚ) : ℝ) ≤ stT323 141 := by
  have hc : ((-100647/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10595009043/156250000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-100647/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c142 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((76841/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37347/100000) (δ := 4083/250000000) (ψ := 3441/250000) 323 255
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t142 : ((64399589121/10000000000000 : ℚ) : ℝ) ≤ stT323 142 := by
  have hc : ((76741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64399589121/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((76741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c143 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((143191/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 483003/2500000) (δ := 4083/250000000) (ψ := 3441/250000) 323 255
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t143 : ((59862801691/1000000000000 : ℚ) : ℝ) ≤ stT323 143 := by
  have hc : ((143171/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59862801691/1000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((143171/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c144 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-496527/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1889789/2500000) (δ := 16171/1000000000) (ψ := 3441/250000) 323 255
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t144 : ((-206907248859/2500000000000 : ℚ) : ℝ) ≤ stT323 144 := by
  have hc : ((-496577/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206907248859/2500000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-496577/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c145 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((519781/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2560503/10000000) (δ := 16339/1000000000) (ψ := 3441/250000) 323 256
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t145 : ((215785582587/5000000000000 : ℚ) : ℝ) ≤ stT323 145 := by
  have hc : ((519681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215785582587/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((519681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c146 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((4579/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2989363/10000000) (δ := 2033/125000000) (ψ := 3441/250000) 323 256
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t146 : ((3030855031/100000000000 : ℚ) : ℝ) ≤ stT323 146 := by
  have hc : ((18311/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3030855031/100000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((18311/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c147 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-241667/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3603343/5000000) (δ := 127/7812500) (ψ := 3441/250000) 323 257
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t147 : ((-49836104901/625000000000 : ℚ) : ℝ) ≤ stT323 147 := by
  have hc : ((-60423/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49836104901/625000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-60423/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c148 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((769441/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -866039/5000000) (δ := 4039/250000000) (ψ := 3441/250000) 323 257
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t148 : ((316196842977/5000000000000 : ℚ) : ℝ) ≤ stT323 148 := by
  have hc : ((769341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316196842977/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((769341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c149 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((44199/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 926427/2500000) (δ := 16247/1000000000) (ψ := 3441/250000) 323 257
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t149 : ((36168229419/5000000000000 : ℚ) : ℝ) ≤ stT323 149 := by
  have hc : ((44149/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36168229419/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((44149/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c150 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-219251/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6600969/10000000) (δ := 16249/1000000000) (ψ := 3441/250000) 323 258
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t150 : ((-44759549043/625000000000 : ℚ) : ℝ) ≤ stT323 150 := by
  have hc : ((-54819/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44759549043/625000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-54819/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c151 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((880357/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -617727/5000000) (δ := 8127/500000000) (ψ := 3441/250000) 323 258
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t151 : ((179085645879/2500000000000 : ℚ) : ℝ) ≤ stT323 151 := by
  have hc : ((880257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179085645879/2500000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((880257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c152 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-33499/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4094611/10000000) (δ := 8077/500000000) (ψ := 3441/250000) 323 258
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t152 : ((-6802965573/1250000000000 : ℚ) : ℝ) ≤ stT323 152 := by
  have hc : ((-33549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6802965573/1250000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-33549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c153 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-408591/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1579563/2500000) (δ := 8121/500000000) (ψ := 3441/250000) 323 259
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t153 : ((-330367042373/5000000000000 : ℚ) : ℝ) ≤ stT323 153 := by
  have hc : ((-408641/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330367042373/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-408641/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c154 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((5699/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33051/312500) (δ := 8171/500000000) (ψ := 3441/250000) 323 259
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t154 : ((18367503757/250000000000 : ℚ) : ℝ) ≤ stT323 154 := by
  have hc : ((45587/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18367503757/250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((45587/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c155 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-48309/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 260557/625000) (δ := 8121/500000000) (ψ := 3441/250000) 323 259
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t155 : ((-1942145799/250000000000 : ℚ) : ℝ) ≤ stT323 155 := by
  have hc : ((-48359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1942145799/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-48359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c156 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-823551/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6346099/10000000) (δ := 4067/250000000) (ψ := 3441/250000) 323 260
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t156 : ((-659448760291/10000000000000 : ℚ) : ℝ) ≤ stT323 156 := by
  have hc : ((-823651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-659448760291/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-823651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c157 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((444753/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37073/312500) (δ := 3247/200000000) (ψ := 3441/250000) 323 260
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t157 : ((177455619229/2500000000000 : ℚ) : ℝ) ≤ stT323 157 := by
  have hc : ((444703/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((177455619229/2500000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((444703/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c158 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-5461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3940643/10000000) (δ := 3247/200000000) (ψ := 3441/250000) 323 260
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t158 : ((-2212049019/5000000000000 : ℚ) : ℝ) ≤ stT323 158 := by
  have hc : ((-5561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2212049019/5000000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-5561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c159 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-890417/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6672641/10000000) (δ := 647/40000000) (ψ := 3441/250000) 323 261
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t159 : ((-176556571971/2500000000000 : ℚ) : ℝ) ≤ stT323 159 := by
  have hc : ((-890517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176556571971/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-890517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c160 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((159943/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1609939/10000000) (δ := 647/40000000) (ψ := 3441/250000) 323 261
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t160 : ((126430166187/2000000000000 : ℚ) : ℝ) ≤ stT323 160 := by
  have hc : ((159923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126430166187/2000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((159923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c161 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((200943/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 342119/1000000) (δ := 651/40000000) (ψ := 3441/250000) 323 261
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t161 : ((15828637673/1000000000000 : ℚ) : ℝ) ≤ stT323 161 := by
  have hc : ((200843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15828637673/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((200843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c162 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-974369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3643367/5000000) (δ := 51/3125000) (ψ := 3441/250000) 323 262
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t162 : ((-30624637263/400000000000 : ℚ) : ℝ) ≤ stT323 162 := by
  have hc : ((-974469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30624637263/400000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-974469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c163 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((600249/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2317459/10000000) (δ := 16283/1000000000) (ψ := 3441/250000) 323 262
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t163 : ((23503635287/500000000000 : ℚ) : ℝ) ≤ stT323 163 := by
  have hc : ((600149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23503635287/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((600149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c164 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((498829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 655343/2500000) (δ := 811/50000000) (ψ := 3441/250000) 323 262
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t164 : ((97360379193/2500000000000 : ℚ) : ℝ) ≤ stT323 164 := by
  have hc : ((498729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97360379193/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((498729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c165 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-991623/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1506033/2000000) (δ := 16283/1000000000) (ψ := 3441/250000) 323 262
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t165 : ((-772055363777/10000000000000 : ℚ) : ℝ) ≤ stT323 165 := by
  have hc : ((-991723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-772055363777/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-991723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c166 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((124351/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3298641/10000000) (δ := 1629/100000000) (ψ := 3441/250000) 323 263
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t166 : ((1929524423/100000000000 : ℚ) : ℝ) ≤ stT323 166 := by
  have hc : ((124301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1929524423/100000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((124301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c167 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((40679/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 387821/2500000) (δ := 16313/1000000000) (ψ := 3441/250000) 323 263
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t167 : ((15737238351/250000000000 : ℚ) : ℝ) ≤ stT323 167 := by
  have hc : ((20337/25000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15737238351/250000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((20337/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c168 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-165883/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318607/500000) (δ := 16213/1000000000) (ψ := 3441/250000) 323 263
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t168 : ((-127996984851/2000000000000 : ℚ) : ℝ) ≤ stT323 168 := by
  have hc : ((-165903/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127996984851/2000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-165903/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c169 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-244101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283967/625000) (δ := 16197/1000000000) (ψ := 3441/250000) 323 264
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t169 : ((-187846979431/10000000000000 : ℚ) : ℝ) ≤ stT323 169 := by
  have hc : ((-244201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-187846979431/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-244201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c170 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((62257/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27567/1250000) (δ := 16297/1000000000) (ψ := 3441/250000) 323 264
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t170 : ((47744084223/625000000000 : ℚ) : ℝ) ≤ stT323 170 := by
  have hc : ((249003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47744084223/625000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((249003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c171 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-400301/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1239151/2500000) (δ := 16197/1000000000) (ψ := 3441/250000) 323 264
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t171 : ((-3827433159/125000000000 : ℚ) : ℝ) ≤ stT323 171 := by
  have hc : ((-400401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3827433159/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-400401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c172 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-374439/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1510727/2500000) (δ := 16299/1000000000) (ψ := 3441/250000) 323 265
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t172 : ((-285545241077/5000000000000 : ℚ) : ℝ) ≤ stT323 172 := by
  have hc : ((-374489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285545241077/5000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-374489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c173 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((855283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1361749/10000000) (δ := 1019/62500000) (ψ := 3441/250000) 323 265
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t173 : ((130036561431/2000000000000 : ℚ) : ℝ) ≤ stT323 173 := by
  have hc : ((855183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130036561431/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((855183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c174 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((7847/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1646219/5000000) (δ := 16299/1000000000) (ψ := 3441/250000) 323 265
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t174 : ((23785703799/1250000000000 : ℚ) : ℝ) ≤ stT323 174 := by
  have hc : ((62751/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23785703799/1250000000000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((62751/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c175 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-249913/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1557597/2000000) (δ := 4073/250000000) (ψ := 3441/250000) 323 266
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t175 : ((-94467691201/1250000000000 : ℚ) : ℝ) ≤ stT323 175 := by
  have hc : ((-124969/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94467691201/1250000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-124969/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c176 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((1167/4000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63737/200000) (δ := 4073/250000000) (ψ := 3441/250000) 323 266
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t176 : ((2198393537/100000000000 : ℚ) : ℝ) ≤ stT323 176 := by
  have hc : ((5833/20000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2198393537/100000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((5833/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c177 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((169947/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 347071/2500000) (δ := 16211/1000000000) (ψ := 3441/250000) 323 266
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t177 : ((63862474921/1000000000000 : ℚ) : ℝ) ≤ stT323 177 := by
  have hc : ((169927/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63862474921/1000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((169927/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c178 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-7203/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5937577/10000000) (δ := 4073/250000000) (ψ := 3441/250000) 323 266
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t178 : ((-337476783/6250000000 : ℚ) : ℝ) ≤ stT323 178 := by
  have hc : ((-1801/2500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337476783/6250000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-1801/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c179 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-503647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5246529/10000000) (δ := 3257/200000000) (ψ := 3441/250000) 323 267
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t179 : ((-94129660673/2500000000000 : ℚ) : ℝ) ≤ stT323 179 := by
  have hc : ((-503747/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94129660673/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-503747/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c180 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((955579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -373973/5000000) (δ := 8109/500000000) (ψ := 3441/250000) 323 267
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t180 : ((142434210009/2000000000000 : ℚ) : ℝ) ≤ stT323 180 := by
  have hc : ((955479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142434210009/2000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((955479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c181 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((80403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 745153/2000000) (δ := 3257/200000000) (ψ := 3441/250000) 323 267
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t181 : ((29844369041/5000000000000 : ℚ) : ℝ) ≤ stT323 181 := by
  have hc : ((80303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29844369041/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((80303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c182 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-991779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1883299/2500000) (δ := 16177/1000000000) (ψ := 3441/250000) 323 268
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t182 : ((-588184247/8000000000 : ℚ) : ℝ) ≤ stT323 182 := by
  have hc : ((-991879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-588184247/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-991879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c183 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((321579/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6217/20000) (δ := 16277/1000000000) (ψ := 3441/250000) 323 268
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t183 : ((237644027859/10000000000000 : ℚ) : ℝ) ≤ stT323 183 := by
  have hc : ((321479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237644027859/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((321479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c184 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((434697/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 323013/2500000) (δ := 16277/1000000000) (ψ := 3441/250000) 323 268
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t184 : ((320425680223/5000000000000 : ℚ) : ℝ) ≤ stT323 184 := by
  have hc : ((434647/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320425680223/5000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((434647/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c185 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-641703/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5668783/10000000) (δ := 16177/1000000000) (ψ := 3441/250000) 323 268
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t185 : ((-94372638529/2000000000000 : ℚ) : ℝ) ≤ stT323 185 := by
  have hc : ((-641803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).2
  have h0 : (0:ℝ) ≤ ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94372638529/2000000000000 : ℚ) : ℝ)
      = ((147043/2000000 : ℚ) : ℝ) * ((-641803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c186 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-647003/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5686109/10000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 269
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t186 : ((-118619803827/2500000000000 : ℚ) : ℝ) ≤ stT323 186 := by
  have hc : ((-647103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118619803827/2500000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-647103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c187 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((214103/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -678147/5000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 269
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t187 : ((9784327951/156250000000 : ℚ) : ℝ) ≤ stT323 187 := by
  have hc : ((107039/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).1
  have hw2 : ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91409/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9784327951/156250000000 : ℚ) : ℝ)
      = ((91409/1250000 : ℚ) : ℝ) * ((107039/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c188 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((380797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1475173/5000000) (δ := 16333/1000000000) (ψ := 3441/250000) 323 269
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t188 : ((69412864707/2500000000000 : ℚ) : ℝ) ≤ stT323 188 := by
  have hc : ((380697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69412864707/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((380697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c189 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-242357/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3617107/5000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 269
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t189 : ((-88153485063/1250000000000 : ℚ) : ℝ) ≤ stT323 189 := by
  have hc : ((-121191/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-88153485063/1250000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-121191/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c190 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-1781/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053143/2500000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 270
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t190 : ((-20691329517/2500000000000 : ℚ) : ℝ) ≤ stT323 190 := by
  have hc : ((-28521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20691329517/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-28521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c191 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((199989/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26319/10000000) (δ := 817/50000000) (ψ := 3441/250000) 323 270
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t191 : ((72346184603/1000000000000 : ℚ) : ℝ) ≤ stT323 191 := by
  have hc : ((199969/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72346184603/1000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((199969/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c192 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-126069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4243003/10000000) (δ := 203/12500000) (ψ := 3441/250000) 323 270
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t192 : ((-11381831659/1250000000000 : ℚ) : ℝ) ≤ stT323 192 := by
  have hc : ((-126169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11381831659/1250000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-126169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c193 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-121607/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7270159/10000000) (δ := 16347/1000000000) (ψ := 3441/250000) 323 271
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t193 : ((-21885915503/312500000000 : ℚ) : ℝ) ≤ stT323 193 := by
  have hc : ((-243239/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21885915503/312500000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-243239/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c194 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((325931/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3096999/10000000) (δ := 16347/1000000000) (ψ := 3441/250000) 323 271
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t194 : ((116966486549/5000000000000 : ℚ) : ℝ) ≤ stT323 194 := by
  have hc : ((325831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116966486549/5000000000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((325831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c195 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((228081/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1054681/10000000) (δ := 4039/250000000) (ψ := 3441/250000) 323 271
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t195 : ((10207130899/156250000000 : ℚ) : ℝ) ≤ stT323 195 := by
  have hc : ((28507/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10207130899/156250000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((28507/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c196 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-241139/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296281/2500000) (δ := 127/7812500) (ψ := 3441/250000) 323 271
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t196 : ((-86138963027/2500000000000 : ℚ) : ℝ) ≤ stT323 196 := by
  have hc : ((-241189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86138963027/2500000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-241189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c197 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-838519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6413391/10000000) (δ := 16249/1000000000) (ψ := 3441/250000) 323 272
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t197 : ((-597491717549/10000000000000 : ℚ) : ℝ) ≤ stT323 197 := by
  have hc : ((-838619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-597491717549/10000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-838619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c198 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((298953/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290597/1250000) (δ := 8077/500000000) (ψ := 3441/250000) 323 272
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t198 : ((212421096107/5000000000000 : ℚ) : ℝ) ≤ stT323 198 := by
  have hc : ((298903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212421096107/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((298903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c199 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((38329/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1743247/10000000) (δ := 16349/1000000000) (ψ := 3441/250000) 323 272
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t199 : ((6791788861/125000000000 : ℚ) : ℝ) ≤ stT323 199 := by
  have hc : ((9581/12500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6791788861/125000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((9581/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c200 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-678369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5790841/10000000) (δ := 16249/1000000000) (ψ := 3441/250000) 323 272
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t200 : ((-479750179183/10000000000000 : ℚ) : ℝ) ≤ stT323 200 := by
  have hc : ((-678469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-479750179183/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-678469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c201 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-353433/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1177927/2000000) (δ := 8081/500000000) (ψ := 3441/250000) 323 273
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t201 : ((-124663910059/2500000000000 : ℚ) : ℝ) ≤ stT323 201 := by
  have hc : ((-353483/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124663910059/2500000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-353483/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c202 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((182427/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -376451/2000000) (δ := 16241/1000000000) (ψ := 3441/250000) 323 273
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t202 : ((64168749997/1250000000000 : ℚ) : ℝ) ≤ stT323 202 := by
  have hc : ((91201/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64168749997/1250000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((91201/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c203 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((332923/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1052711/5000000) (δ := 16341/1000000000) (ψ := 3441/250000) 323 273
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t203 : ((116815454763/2500000000000 : ℚ) : ℝ) ≤ stT323 203 := by
  have hc : ((332873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116815454763/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((332873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c204 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-30277/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6073477/10000000) (δ := 16341/1000000000) (ψ := 3441/250000) 323 273
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t204 : ((-21200969621/400000000000 : ℚ) : ℝ) ≤ stT323 204 := by
  have hc : ((-30281/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21200969621/400000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-30281/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c205 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-10108/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5685811/10000000) (δ := 8117/500000000) (ψ := 3441/250000) 323 274
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t205 : ((-112973309543/2500000000000 : ℚ) : ℝ) ≤ stT323 205 := by
  have hc : ((-161753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112973309543/2500000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-161753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c206 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((381601/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -878177/5000000) (δ := 16269/1000000000) (ψ := 3441/250000) 323 274
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t206 : ((265839172883/5000000000000 : ℚ) : ℝ) ≤ stT323 206 := by
  have hc : ((381551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((265839172883/5000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((381551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c207 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((65121/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 430809/2000000) (δ := 8117/500000000) (ψ := 3441/250000) 323 274
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t207 : ((5656908791/125000000000 : ℚ) : ℝ) ≤ stT323 207 := by
  have hc : ((65111/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5656908791/125000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((65111/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c208 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-749599/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604563/1000000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 274
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t208 : ((-4061119483/78125000000 : ℚ) : ℝ) ≤ stT323 208 := by
  have hc : ((-749699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4061119483/78125000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-749699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c209 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-338973/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2894701/5000000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 275
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t209 : ((-46901458889/1000000000000 : ℚ) : ℝ) ≤ stT323 209 := by
  have hc : ((-339023/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46901458889/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-339023/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c210 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((715131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -967481/5000000) (δ := 1011/62500000) (ψ := 3441/250000) 323 275
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t210 : ((98683573403/2000000000000 : ℚ) : ℝ) ≤ stT323 210 := by
  have hc : ((715031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98683573403/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((715031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c211 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((18113/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1901147/10000000) (δ := 16327/1000000000) (ψ := 3441/250000) 323 275
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t211 : ((6233887647/125000000000 : ℚ) : ℝ) ≤ stT323 211 := by
  have hc : ((36221/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6233887647/125000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((36221/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c212 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-131401/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 357443/625000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 275
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t212 : ((-90260337063/2000000000000 : ℚ) : ℝ) ≤ stT323 212 := by
  have hc : ((-131421/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-90260337063/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-131421/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c213 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-78627/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6188861/10000000) (δ := 811/50000000) (ψ := 3441/250000) 323 276
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t213 : ((-53881207393/1000000000000 : ℚ) : ℝ) ≤ stT323 213 := by
  have hc : ((-78637/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53881207393/1000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-78637/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c214 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((571351/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601653/2500000) (δ := 51/3125000) (ψ := 3441/250000) 323 276
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t214 : ((78099722967/2000000000000 : ℚ) : ℝ) ≤ stT323 214 := by
  have hc : ((571251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78099722967/2000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((571251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c215 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((856069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1357953/10000000) (δ := 51/3125000) (ψ := 3441/250000) 323 276
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t215 : ((291882861093/5000000000000 : ℚ) : ℝ) ≤ stT323 215 := by
  have hc : ((855969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291882861093/5000000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((855969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c216 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-226993/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1276269/2500000) (δ := 51/3125000) (ψ := 3441/250000) 323 276
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t216 : ((-77241617901/2500000000000 : ℚ) : ℝ) ≤ stT323 216 := by
  have hc : ((-227043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77241617901/2500000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-227043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c217 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-57751/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10997/16000) (δ := 1619/100000000) (ψ := 3441/250000) 323 277
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t217 : ((-31366576301/500000000000 : ℚ) : ℝ) ≤ stT323 217 := by
  have hc : ((-231029/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31366576301/500000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-231029/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c218 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((150911/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1580241/5000000) (δ := 1629/100000000) (ψ := 3441/250000) 323 277
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t218 : ((20435178477/1000000000000 : ℚ) : ℝ) ≤ stT323 218 := by
  have hc : ((150861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20435178477/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((150861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c219 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((244293/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 535203/10000000) (δ := 1619/100000000) (ψ := 3441/250000) 323 277
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t219 : ((41265231379/625000000000 : ℚ) : ℝ) ≤ stT323 219 := by
  have hc : ((61067/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41265231379/625000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((61067/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c220 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-28639/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4214011/10000000) (δ := 16313/1000000000) (ψ := 3441/250000) 323 277
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t220 : ((-12078293/1562500000 : ℚ) : ℝ) ≤ stT323 220 := by
  have hc : ((-3583/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12078293/1562500000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-3583/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c221 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-999961/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3915889/5000000) (δ := 8103/500000000) (ψ := 3441/250000) 323 278
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t221 : ((-672714033053/10000000000000 : ℚ) : ℝ) ≤ stT323 221 := by
  have hc : ((-1000061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-672714033053/10000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-1000061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c222 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-103513/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2093119/5000000) (δ := 16297/1000000000) (ψ := 3441/250000) 323 278
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t222 : ((-69540590241/10000000000000 : ℚ) : ℝ) ≤ stT323 222 := by
  have hc : ((-103613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69540590241/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-103613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c223 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((487641/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55701/1000000) (δ := 16297/1000000000) (ψ := 3441/250000) 323 278
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t223 : ((326514825559/5000000000000 : ℚ) : ℝ) ≤ stT323 223 := by
  have hc : ((487591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).1
  have hw2 : ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((669649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((326514825559/5000000000000 : ℚ) : ℝ)
      = ((669649/10000000 : ℚ) : ℝ) * ((487591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c224 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((85349/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3055987/10000000) (δ := 16197/1000000000) (ψ := 3441/250000) 323 278
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t224 : ((14252371643/625000000000 : ℚ) : ℝ) ≤ stT323 224 := by
  have hc : ((21331/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14252371643/625000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((21331/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c225 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-443399/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1330583/2000000) (δ := 16197/1000000000) (ψ := 3441/250000) 323 278
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t225 : ((-295632814483/5000000000000 : ℚ) : ℝ) ≤ stT323 225 := by
  have hc : ((-443449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295632814483/5000000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-443449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c226 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-58011/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5474149/10000000) (δ := 6481/200000000) (ψ := 3441/250000) 323 279
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t226 : ((-38595047011/1000000000000 : ℚ) : ℝ) ≤ stT323 226 := by
  have hc : ((-58021/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38595047011/1000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-58021/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c227 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((45147/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -477249/2500000) (δ := 3261/200000000) (ψ := 3441/250000) 323 279
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t227 : ((119843816049/2500000000000 : ℚ) : ℝ) ≤ stT323 227 := by
  have hc : ((180563/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119843816049/2500000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((180563/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c228 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((99041/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1640451/10000000) (δ := 3261/200000000) (ψ := 3441/250000) 323 279
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t228 : ((65583208581/1250000000000 : ℚ) : ℝ) ≤ stT323 228 := by
  have hc : ((198057/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65583208581/1250000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((198057/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c229 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-239257/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2587197/5000000) (δ := 3261/200000000) (ψ := 3441/250000) 323 279
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t229 : ((-158138612433/5000000000000 : ℚ) : ℝ) ≤ stT323 229 := by
  have hc : ((-239307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158138612433/5000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-239307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c230 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-472111/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140301/200000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 280
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t230 : ((-311333992341/5000000000000 : ℚ) : ℝ) ≤ stT323 230 := by
  have hc : ((-472161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311333992341/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-472161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c231 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((165317/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -219487/625000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 280
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t231 : ((108704690367/10000000000000 : ℚ) : ℝ) ≤ stT323 231 := by
  have hc : ((165217/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108704690367/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((165217/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c232 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((199991/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4743/2000000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 280
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t232 : ((32821840143/500000000000 : ℚ) : ℝ) ≤ stT323 232 := by
  have hc : ((199971/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32821840143/500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((199971/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c233 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((189867/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3449423/10000000) (δ := 16291/1000000000) (ψ := 3441/250000) 323 280
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t233 : ((124320346807/10000000000000 : ℚ) : ℝ) ≤ stT323 233 := by
  have hc : ((189767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124320346807/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((189767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c234 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-14519/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 863463/1250000) (δ := 2039/125000000) (ψ := 3441/250000) 323 280
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t234 : ((-151878346209/2500000000000 : ℚ) : ℝ) ≤ stT323 234 := by
  have hc : ((-232329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151878346209/2500000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-232329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c235 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-135309/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5356757/10000000) (δ := 4071/250000000) (ψ := 3441/250000) 323 281
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t235 : ((-44141146443/1250000000000 : ℚ) : ℝ) ≤ stT323 235 := by
  have hc : ((-67667/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44141146443/1250000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-67667/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c236 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((717111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1927869/10000000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 281
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t236 : ((7292718881/156250000000 : ℚ) : ℝ) ≤ stT323 236 := by
  have hc : ((717011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7292718881/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((717011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c237 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((103547/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1486483/10000000) (δ := 16219/1000000000) (ψ := 3441/250000) 323 281
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t237 : ((134505603261/2500000000000 : ℚ) : ℝ) ≤ stT323 237 := by
  have hc : ((207069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134505603261/2500000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((207069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c238 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-93609/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2443231/5000000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 281
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t238 : ((-7586741667/312500000000 : ℚ) : ℝ) ≤ stT323 238 := by
  have hc : ((-46817/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7586741667/312500000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-46817/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c239 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-493019/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1487147/2000000) (δ := 16177/1000000000) (ψ := 3441/250000) 323 282
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t239 : ((-318940203443/5000000000000 : ℚ) : ℝ) ≤ stT323 239 := by
  have hc : ((-493069/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318940203443/5000000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-493069/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c240 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-1713/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4064099/10000000) (δ := 8163/500000000) (ψ := 3441/250000) 323 282
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t240 : ((-4431021021/1250000000000 : ℚ) : ℝ) ≤ stT323 240 := by
  have hc : ((-13729/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4431021021/1250000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-13729/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c241 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((240083/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -353257/5000000) (δ := 8163/500000000) (ψ := 3441/250000) 323 282
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t241 : ((19329350131/312500000000 : ℚ) : ℝ) ≤ stT323 241 := by
  have hc : ((120029/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).1
  have hw2 : ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((161039/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19329350131/312500000000 : ℚ) : ℝ)
      = ((161039/2500000 : ℚ) : ℝ) * ((120029/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c242 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((246669/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1318591/5000000) (δ := 8163/500000000) (ψ := 3441/250000) 323 282
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t242 : ((19816576507/625000000000 : ℚ) : ℝ) ≤ stT323 242 := by
  have hc : ((246619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19816576507/625000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((246619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c243 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-728433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5967069/10000000) (δ := 16277/1000000000) (ψ := 3441/250000) 323 282
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t243 : ((-467354648033/10000000000000 : ℚ) : ℝ) ≤ stT323 243 := by
  have hc : ((-728533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-467354648033/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-728533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c244 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-168193/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6424653/10000000) (δ := 1617/100000000) (ψ := 3441/250000) 323 283
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t244 : ((-21537487881/400000000000 : ℚ) : ℝ) ≤ stT323 244 := by
  have hc : ((-168213/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).2
  have h0 : (0:ℝ) ≤ ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21537487881/400000000000 : ℚ) : ℝ)
      = ((128037/2000000 : ℚ) : ℝ) * ((-168213/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c245 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((158227/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1561009/5000000) (δ := 32433/1000000000) (ψ := 3441/250000) 323 283
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t245 : ((25263872263/1250000000000 : ℚ) : ℝ) ≤ stT323 245 := by
  have hc : ((158177/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25263872263/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((158177/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c246 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((249441/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41803/2500000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 283
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t246 : ((2484713369/39062500000 : ℚ) : ℝ) ≤ stT323 246 := by
  have hc : ((31177/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2484713369/39062500000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((31177/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c247 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((192359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1721539/5000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 283
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t247 : ((30582831389/2500000000000 : ℚ) : ℝ) ≤ stT323 247 := by
  have hc : ((192259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30582831389/2500000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((192259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c248 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-448179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6705701/10000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 283
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t248 : ((-284625863229/5000000000000 : ℚ) : ℝ) ≤ stT323 248 := by
  have hc : ((-448229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-284625863229/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-448229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c249 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-667111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2876401/5000000) (δ := 8131/500000000) (ψ := 3441/250000) 323 284
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t249 : ((-16913131639/400000000000 : ℚ) : ℝ) ≤ stT323 249 := by
  have hc : ((-667211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16913131639/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-667211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c250 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((267409/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2516261/10000000) (δ := 8081/500000000) (ψ := 3441/250000) 323 284
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t250 : ((33818507269/1000000000000 : ℚ) : ℝ) ≤ stT323 250 := by
  have hc : ((267359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33818507269/1000000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((267359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c251 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((960247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 707279/10000000) (δ := 8081/500000000) (ψ := 3441/250000) 323 284
    (log_br_251).1 (log_br_251).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t251 : ((303019512759/5000000000000 : ℚ) : ℝ) ≤ stT323 251 := by
  have hc : ((960147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((251 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c251).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_251).1
  have hw2 : ((251 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((315597/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303019512759/5000000000000 : ℚ) : ℝ)
      = ((315597/5000000 : ℚ) : ℝ) * ((960147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c252 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((901/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 195899/500000) (δ := 16241/1000000000) (ψ := 3441/250000) 323 284
    (log_br_252).1 (log_br_252).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t252 : ((6897843/31250000000 : ℚ) : ℝ) ≤ stT323 252 := by
  have hc : ((219/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((252 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c252).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_252).1
  have hw2 : ((252 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31497/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6897843/31250000000 : ℚ) : ℝ)
      = ((31497/500000 : ℚ) : ℝ) * ((219/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c253 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-478373/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7116003/10000000) (δ := 16241/1000000000) (ψ := 3441/250000) 323 284
    (log_br_253).1 (log_br_253).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t253 : ((-60156429597/1000000000000 : ℚ) : ℝ) ≤ stT323 253 := by
  have hc : ((-478423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((253 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c253).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_253).2
  have h0 : (0:ℝ) ≤ ((253 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60156429597/1000000000000 : ℚ) : ℝ)
      = ((125739/2000000 : ℚ) : ℝ) * ((-478423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c254 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-55787/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2703267/5000000) (δ := 4087/250000000) (ψ := 3441/250000) 323 285
    (log_br_254).1 (log_br_254).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t254 : ((-136758447/3906250000 : ℚ) : ℝ) ≤ stT323 254 := by
  have hc : ((-55797/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((254 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c254).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_254).2
  have h0 : (0:ℝ) ≤ ((254 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136758447/3906250000 : ℚ) : ℝ)
      = ((4902/78125 : ℚ) : ℝ) * ((-55797/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c255 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((626727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17869/80000) (δ := 3251/200000000) (ψ := 3441/250000) 323 285
    (log_br_255).1 (log_br_255).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t255 : ((24525554153/625000000000 : ℚ) : ℝ) ≤ stT323 255 := by
  have hc : ((626627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((255 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c255).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_255).1
  have hw2 : ((255 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39139/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24525554153/625000000000 : ℚ) : ℝ)
      = ((39139/625000 : ℚ) : ℝ) * ((626627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c256 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((932059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18537/200000) (δ := 4087/250000000) (ψ := 3441/250000) 323 285
    (log_br_256).1 (log_br_256).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t256 : ((931959/16000000 : ℚ) : ℝ) ≤ stT323 256 := by
  have hc : ((931959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((256 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c256).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_256).1
  have hw2 : ((256 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/16 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((931959/16000000 : ℚ) : ℝ)
      = ((1/16 : ℚ) : ℝ) * ((931959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c257 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-59157/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4074969/10000000) (δ := 3231/200000000) (ψ := 3441/250000) 323 285
    (log_br_257).1 (log_br_257).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t257 : ((-36963509231/10000000000000 : ℚ) : ℝ) ≤ stT323 257 := by
  have hc : ((-59257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((257 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c257).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_257).2
  have h0 : (0:ℝ) ≤ ((257 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36963509231/10000000000000 : ℚ) : ℝ)
      = ((623783/10000000 : ℚ) : ℝ) * ((-59257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c258 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-967097/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1442179/2000000) (δ := 3251/200000000) (ψ := 3441/250000) 323 285
    (log_br_258).1 (log_br_258).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t258 : ((-602150737881/10000000000000 : ℚ) : ℝ) ≤ stT323 258 := by
  have hc : ((-967197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((258 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c258).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_258).2
  have h0 : (0:ℝ) ≤ ((258 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-602150737881/10000000000000 : ℚ) : ℝ)
      = ((622573/10000000 : ℚ) : ℝ) * ((-967197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c259 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-546773/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2686627/5000000) (δ := 3251/200000000) (ψ := 3441/250000) 323 286
    (log_br_259).1 (log_br_259).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t259 : ((-33981047601/1000000000000 : ℚ) : ℝ) ≤ stT323 259 := by
  have hc : ((-546873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((259 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c259).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_259).2
  have h0 : (0:ℝ) ≤ ((259 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33981047601/1000000000000 : ℚ) : ℝ)
      = ((62137/1000000 : ℚ) : ℝ) * ((-546873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c260 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((618009/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -70671/312500) (δ := 3251/200000000) (ψ := 3441/250000) 323 286
    (log_br_260).1 (log_br_260).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t260 : ((383210478257/10000000000000 : ℚ) : ℝ) ≤ stT323 260 := by
  have hc : ((617909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((260 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c260).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_260).1
  have hw2 : ((260 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((620173/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383210478257/10000000000000 : ℚ) : ℝ)
      = ((620173/10000000 : ℚ) : ℝ) * ((617909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c261 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((944297/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 838359/10000000) (δ := 3251/200000000) (ψ := 3441/250000) 323 286
    (log_br_261).1 (log_br_261).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t261 : ((73055354481/1250000000000 : ℚ) : ℝ) ≤ stT323 261 := by
  have hc : ((944197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((261 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c261).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_261).1
  have hw2 : ((261 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((77373/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73055354481/1250000000000 : ℚ) : ℝ)
      = ((77373/1250000 : ℚ) : ℝ) * ((944197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c262 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3926319/10000000) (δ := 6081/125000000) (ψ := 3441/250000) 323 286
    (log_br_262).1 (log_br_262).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t262 : ((52204269/5000000000000 : ℚ) : ℝ) ≤ stT323 262 := by
  have hc : ((169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((262 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c262).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_262).1
  have hw2 : ((262 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((308901/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52204269/5000000000000 : ℚ) : ℝ)
      = ((308901/5000000 : ℚ) : ℝ) * ((169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c263 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-235639/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7002491/10000000) (δ := 3251/200000000) (ψ := 3441/250000) 323 286
    (log_br_263).1 (log_br_263).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t263 : ((-9082299083/156250000000 : ℚ) : ℝ) ≤ stT323 263 := by
  have hc : ((-14729/15625 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((263 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c263).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_263).2
  have h0 : (0:ℝ) ≤ ((263 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9082299083/156250000000 : ℚ) : ℝ)
      = ((616627/10000000 : ℚ) : ℝ) * ((-14729/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c264 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-316559/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5640929/10000000) (δ := 24281/500000000) (ψ := 3441/250000) 323 287
    (log_br_264).1 (log_br_264).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t264 : ((-97429770961/2500000000000 : ℚ) : ℝ) ≤ stT323 264 := by
  have hc : ((-316609/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((264 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c264).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_264).2
  have h0 : (0:ℝ) ≤ ((264 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97429770961/2500000000000 : ℚ) : ℝ)
      = ((307729/5000000 : ℚ) : ℝ) * ((-316609/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c265 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((510349/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1294007/5000000) (δ := 8081/500000000) (ψ := 3441/250000) 323 287
    (log_br_265).1 (log_br_265).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t265 : ((62688681891/2000000000000 : ℚ) : ℝ) ≤ stT323 265 := by
  have hc : ((510249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((265 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c265).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_265).1
  have hw2 : ((265 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((122859/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62688681891/2000000000000 : ℚ) : ℝ)
      = ((122859/2000000 : ℚ) : ℝ) * ((510249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c266 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((983597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 90687/2000000) (δ := 8131/500000000) (ψ := 3441/250000) 323 287
    (log_br_266).1 (log_br_266).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t266 : ((603020367083/10000000000000 : ℚ) : ℝ) ≤ stT323 266 := by
  have hc : ((983497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((266 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c266).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_266).1
  have hw2 : ((266 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((613139/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((603020367083/10000000000000 : ℚ) : ℝ)
      = ((613139/10000000 : ℚ) : ℝ) * ((983497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c267 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((353/2000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3483417/10000000) (δ := 8081/500000000) (ψ := 3441/250000) 323 287
    (log_br_267).1 (log_br_267).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t267 : ((26988759/2500000000 : ℚ) : ℝ) ≤ stT323 267 := by
  have hc : ((441/2500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((267 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c267).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_267).1
  have hw2 : ((267 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((61199/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26988759/2500000000 : ℚ) : ℝ)
      = ((61199/1000000 : ℚ) : ℝ) * ((441/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c268 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-21433/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3251047/5000000) (δ := 16241/1000000000) (ψ := 3441/250000) 323 287
    (log_br_268).1 (log_br_268).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t268 : ((-818364519/15625000000 : ℚ) : ℝ) ≤ stT323 268 := by
  have hc : ((-42871/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((268 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c268).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_268).2
  have h0 : (0:ℝ) ≤ ((268 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-818364519/15625000000 : ℚ) : ℝ)
      = ((19089/312500 : ℚ) : ℝ) * ((-42871/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c269 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-6309/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -387401/625000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 288
    (log_br_269).1 (log_br_269).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t269 : ((-19235772339/400000000000 : ℚ) : ℝ) ≤ stT323 269 := by
  have hc : ((-31549/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((269 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c269).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_269).2
  have h0 : (0:ℝ) ≤ ((269 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19235772339/400000000000 : ℚ) : ℝ)
      = ((609711/10000000 : ℚ) : ℝ) * ((-31549/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c270 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((71477/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3202107/10000000) (δ := 8167/500000000) (ψ := 3441/250000) 323 288
    (log_br_270).1 (log_br_270).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t270 : ((543553227/31250000000 : ℚ) : ℝ) ≤ stT323 270 := by
  have hc : ((17863/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((270 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c270).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_270).1
  have hw2 : ((270 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((30429/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((543553227/31250000000 : ℚ) : ℝ)
      = ((30429/500000 : ℚ) : ℝ) * ((17863/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c271 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((12453/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10843/500000) (δ := 8117/500000000) (ψ := 3441/250000) 323 288
    (log_br_271).1 (log_br_271).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t271 : ((945486281/15625000000 : ℚ) : ℝ) ≤ stT323 271 := by
  have hc : ((49807/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((271 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c271).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_271).1
  have hw2 : ((271 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((18983/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((945486281/15625000000 : ℚ) : ℝ)
      = ((18983/312500 : ℚ) : ℝ) * ((49807/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c272 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((450983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689331/2500000) (δ := 8117/500000000) (ψ := 3441/250000) 323 288
    (log_br_272).1 (log_br_272).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t272 : ((273387947337/10000000000000 : ℚ) : ℝ) ≤ stT323 272 := by
  have hc : ((450883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((272 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c272).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_272).1
  have hw2 : ((272 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273387947337/10000000000000 : ℚ) : ℝ)
      = ((606339/10000000 : ℚ) : ℝ) * ((450883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c273 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-657463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5720607/10000000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 288
    (log_br_273).1 (log_br_273).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t273 : ((-99493884841/2500000000000 : ℚ) : ℝ) ≤ stT323 273 := by
  have hc : ((-657563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((273 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c273).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_273).2
  have h0 : (0:ℝ) ≤ ((273 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99493884841/2500000000000 : ℚ) : ℝ)
      = ((151307/2500000 : ℚ) : ℝ) * ((-657563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c274 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-236699/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7034813/10000000) (δ := 4069/250000000) (ψ := 3441/250000) 323 289
    (log_br_274).1 (log_br_274).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t274 : ((-35752603263/625000000000 : ℚ) : ℝ) ≤ stT323 274 := by
  have hc : ((-59181/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((274 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c274).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_274).2
  have h0 : (0:ℝ) ≤ ((274 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35752603263/625000000000 : ℚ) : ℝ)
      = ((604123/10000000 : ℚ) : ℝ) * ((-59181/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c275 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-8303/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1023293/2500000) (δ := 16327/1000000000) (ψ := 3441/250000) 323 289
    (log_br_275).1 (log_br_275).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t275 : ((-10028875513/2500000000000 : ℚ) : ℝ) ≤ stT323 275 := by
  have hc : ((-16631/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((275 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c275).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_275).2
  have h0 : (0:ℝ) ≤ ((275 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10028875513/2500000000000 : ℚ) : ℝ)
      = ((603023/10000000 : ℚ) : ℝ) * ((-16631/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c276 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((223473/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290527/2500000) (δ := 1011/62500000) (ψ := 3441/250000) 323 289
    (log_br_276).1 (log_br_276).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t276 : ((16812478899/312500000000 : ℚ) : ℝ) ≤ stT323 276 := by
  have hc : ((27931/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((276 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c276).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_276).1
  have hw2 : ((276 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16812478899/312500000000 : ℚ) : ℝ)
      = ((601929/10000000 : ℚ) : ℝ) * ((27931/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c277 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((762679/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1758377/10000000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 289
    (log_br_277).1 (log_br_277).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t277 : ((458188728939/10000000000000 : ℚ) : ℝ) ≤ stT323 277 := by
  have hc : ((762579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((277 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c277).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_277).1
  have hw2 : ((277 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((600841/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458188728939/10000000000000 : ℚ) : ℝ)
      = ((600841/10000000 : ℚ) : ℝ) * ((762579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c278 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-292191/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1167071/2500000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 289
    (log_br_278).1 (log_br_278).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t278 : ((-175304742451/10000000000000 : ℚ) : ℝ) ≤ stT323 278 := by
  have hc : ((-292291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((278 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c278).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_278).2
  have h0 : (0:ℝ) ≤ ((278 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175304742451/10000000000000 : ℚ) : ℝ)
      = ((599761/10000000 : ℚ) : ℝ) * ((-292291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c279 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-19869/20000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3783847/5000000) (δ := 4069/250000000) (ψ := 3441/250000) 323 289
    (log_br_279).1 (log_br_279).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t279 : ((-2379293927/40000000000 : ℚ) : ℝ) ≤ stT323 279 := by
  have hc : ((-19871/20000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((279 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c279).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_279).2
  have h0 : (0:ℝ) ≤ ((279 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2379293927/40000000000 : ℚ) : ℝ)
      = ((119737/2000000 : ℚ) : ℝ) * ((-19871/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c280 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-505231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1050223/2000000) (δ := 4071/250000000) (ψ := 3441/250000) 323 290
    (log_br_280).1 (log_br_280).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t280 : ((-60398677113/2000000000000 : ℚ) : ℝ) ≤ stT323 280 := by
  have hc : ((-505331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((280 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c280).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_280).2
  have h0 : (0:ℝ) ≤ ((280 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60398677113/2000000000000 : ℚ) : ℝ)
      = ((119523/2000000 : ℚ) : ℝ) * ((-505331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c281 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((72817/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1186189/5000000) (δ := 16219/1000000000) (ψ := 3441/250000) 323 290
    (log_br_281).1 (log_br_281).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t281 : ((86862903341/2500000000000 : ℚ) : ℝ) ≤ stT323 281 := by
  have hc : ((145609/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((281 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c281).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_281).1
  have hw2 : ((281 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((596549/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86862903341/2500000000000 : ℚ) : ℝ)
      = ((596549/10000000 : ℚ) : ℝ) * ((145609/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c282 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((980369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 99237/2000000) (δ := 16219/1000000000) (ψ := 3441/250000) 323 290
    (log_br_282).1 (log_br_282).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t282 : ((583741367079/10000000000000 : ℚ) : ℝ) ≤ stT323 282 := by
  have hc : ((980269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((282 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c282).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_282).1
  have hw2 : ((282 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((595491/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((583741367079/10000000000000 : ℚ) : ℝ)
      = ((595491/10000000 : ℚ) : ℝ) * ((980269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c283 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((226971/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1677287/5000000) (δ := 4071/250000000) (ψ := 3441/250000) 323 290
    (log_br_283).1 (log_br_283).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t283 : ((67430371749/5000000000000 : ℚ) : ℝ) ≤ stT323 283 := by
  have hc : ((226871/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((283 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c283).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_283).1
  have hw2 : ((283 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((297219/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67430371749/5000000000000 : ℚ) : ℝ)
      = ((297219/5000000 : ℚ) : ℝ) * ((226871/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c284 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-789739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6202949/10000000) (δ := 16219/1000000000) (ψ := 3441/250000) 323 290
    (log_br_284).1 (log_br_284).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t284 : ((-468683354049/10000000000000 : ℚ) : ℝ) ≤ stT323 284 := by
  have hc : ((-789839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((284 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c284).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_284).2
  have h0 : (0:ℝ) ≤ ((284 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-468683354049/10000000000000 : ℚ) : ℝ)
      = ((593391/10000000 : ℚ) : ℝ) * ((-789839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c285 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-889339/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1666683/2500000) (δ := 16291/1000000000) (ψ := 3441/250000) 323 291
    (log_br_285).1 (log_br_285).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t285 : ((-526858302211/10000000000000 : ℚ) : ℝ) ≤ stT323 285 := by
  have hc : ((-889439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((285 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c285).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_285).2
  have h0 : (0:ℝ) ≤ ((285 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-526858302211/10000000000000 : ℚ) : ℝ)
      = ((592349/10000000 : ℚ) : ℝ) * ((-889439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c286 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((8867/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1919151/5000000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 291
    (log_br_286).1 (log_br_286).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t286 : ((163386897/78125000000 : ℚ) : ℝ) ≤ stT323 286 := by
  have hc : ((4421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((286 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c286).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_286).1
  have hw2 : ((286 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((36957/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163386897/78125000000 : ℚ) : ℝ)
      = ((36957/625000 : ℚ) : ℝ) * ((4421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c287 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((917947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -254951/2500000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 291
    (log_br_287).1 (log_br_287).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t287 : ((541787645007/10000000000000 : ℚ) : ℝ) ≤ stT323 287 := by
  have hc : ((917847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((287 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c287).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_287).1
  have hw2 : ((287 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((590281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((541787645007/10000000000000 : ℚ) : ℝ)
      = ((590281/10000000 : ℚ) : ℝ) * ((917847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c288 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((754741/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 894421/5000000) (δ := 2039/125000000) (ψ := 3441/250000) 323 291
    (log_br_288).1 (log_br_288).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t288 : ((88935196491/2000000000000 : ℚ) : ℝ) ≤ stT323 288 := by
  have hc : ((754641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((288 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c288).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_288).1
  have hw2 : ((288 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88935196491/2000000000000 : ℚ) : ℝ)
      = ((117851/2000000 : ℚ) : ℝ) * ((754641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c289 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-32657/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4587799/10000000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 291
    (log_br_289).1 (log_br_289).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t289 : ((-9608688001/625000000000 : ℚ) : ℝ) ≤ stT323 289 := by
  have hc : ((-65339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((289 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c289).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_289).2
  have h0 : (0:ℝ) ≤ ((289 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9608688001/625000000000 : ℚ) : ℝ)
      = ((147059/2500000 : ℚ) : ℝ) * ((-65339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c290 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-196373/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3688573/5000000) (δ := 4053/250000000) (ψ := 3441/250000) 323 291
    (log_br_290).1 (log_br_290).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t290 : ((-115326093853/2000000000000 : ℚ) : ℝ) ≤ stT323 290 := by
  have hc : ((-196393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((290 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c290).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_290).2
  have h0 : (0:ℝ) ≤ ((290 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115326093853/2000000000000 : ℚ) : ℝ)
      = ((587221/10000000 : ℚ) : ℝ) * ((-196393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c291 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-302461/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138779/250000) (δ := 3241/200000000) (ψ := 3441/250000) 323 292
    (log_br_291).1 (log_br_291).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t291 : ((-177335275821/5000000000000 : ℚ) : ℝ) ≤ stT323 291 := by
  have hc : ((-302511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((291 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c291).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_291).2
  have h0 : (0:ℝ) ≤ ((291 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177335275821/5000000000000 : ℚ) : ℝ)
      = ((586211/10000000 : ℚ) : ℝ) * ((-302511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c292 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((13829/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55619/200000) (δ := 8149/500000000) (ψ := 3441/250000) 323 292
    (log_br_292).1 (log_br_292).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t292 : ((12945553887/500000000000 : ℚ) : ℝ) ≤ stT323 292 := by
  have hc : ((110607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((292 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c292).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_292).1
  have hw2 : ((292 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117041/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12945553887/500000000000 : ℚ) : ℝ)
      = ((117041/2000000 : ℚ) : ℝ) * ((110607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c293 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((999967/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20269/10000000) (δ := 8149/500000000) (ψ := 3441/250000) 323 292
    (log_br_293).1 (log_br_293).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t293 : ((292064150301/5000000000000 : ℚ) : ℝ) ≤ stT323 293 := by
  have hc : ((999867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((293 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c293).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_293).1
  have hw2 : ((293 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((292103/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292064150301/5000000000000 : ℚ) : ℝ)
      = ((292103/5000000 : ℚ) : ℝ) * ((999867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c294 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((460369/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 682741/2500000) (δ := 8099/500000000) (ψ := 3441/250000) 323 292
    (log_br_294).1 (log_br_294).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t294 : ((268433943759/10000000000000 : ℚ) : ℝ) ≤ stT323 294 := by
  have hc : ((460269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((294 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c294).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_294).1
  have hw2 : ((294 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((583211/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268433943759/10000000000000 : ℚ) : ℝ)
      = ((583211/10000000 : ℚ) : ℝ) * ((460269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c295 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-289853/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5472911/10000000) (δ := 8099/500000000) (ψ := 3441/250000) 323 292
    (log_br_295).1 (log_br_295).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t295 : ((-168788194369/5000000000000 : ℚ) : ℝ) ≤ stT323 295 := by
  have hc : ((-289903/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((295 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c295).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_295).2
  have h0 : (0:ℝ) ≤ ((295 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168788194369/5000000000000 : ℚ) : ℝ)
      = ((582223/10000000 : ℚ) : ℝ) * ((-289903/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c296 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-990127/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -937799/1250000) (δ := 8149/500000000) (ψ := 3441/250000) 323 293
    (log_br_296).1 (log_br_296).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t296 : ((-575558551253/10000000000000 : ℚ) : ℝ) ≤ stT323 296 := by
  have hc : ((-990227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((296 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c296).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_296).2
  have h0 : (0:ℝ) ≤ ((296 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-575558551253/10000000000000 : ℚ) : ℝ)
      = ((581239/10000000 : ℚ) : ℝ) * ((-990227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c297 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-334221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -597367/1250000) (δ := 3261/200000000) (ψ := 3441/250000) 323 293
    (log_br_297).1 (log_br_297).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t297 : ((-193992769139/10000000000000 : ℚ) : ℝ) ≤ stT323 297 := by
  have hc : ((-334321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((297 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c297).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_297).2
  have h0 : (0:ℝ) ≤ ((297 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-193992769139/10000000000000 : ℚ) : ℝ)
      = ((580259/10000000 : ℚ) : ℝ) * ((-334321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c298 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((338957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2064687/10000000) (δ := 8149/500000000) (ψ := 3441/250000) 323 293
    (log_br_298).1 (log_br_298).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t298 : ((49080850647/1250000000000 : ℚ) : ℝ) ≤ stT323 298 := by
  have hc : ((338907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((298 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c298).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_298).1
  have hw2 : ((298 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((144821/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49080850647/1250000000000 : ℚ) : ℝ)
      = ((144821/2500000 : ℚ) : ℝ) * ((338907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c299 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((483679/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 640519/10000000) (δ := 8099/500000000) (ψ := 3441/250000) 323 293
    (log_br_299).1 (log_br_299).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t299 : ((139844710753/2500000000000 : ℚ) : ℝ) ≤ stT323 299 := by
  have hc : ((483629/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((299 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c299).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_299).1
  have hw2 : ((299 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((289157/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139844710753/2500000000000 : ℚ) : ℝ)
      = ((289157/5000000 : ℚ) : ℝ) * ((483629/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c300 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((14621/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3336681/10000000) (δ := 3241/200000000) (ψ := 3441/250000) 323 293
    (log_br_300).1 (log_br_300).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t300 : ((675026073/50000000000 : ℚ) : ℝ) ≤ stT323 300 := by
  have hc : ((58459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((300 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c300).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_300).1
  have hw2 : ((300 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((675026073/50000000000 : ℚ) : ℝ)
      = ((11547/200000 : ℚ) : ℝ) * ((58459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c301 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-185953/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6023879/10000000) (δ := 8149/500000000) (ψ := 3441/250000) 323 293
    (log_br_301).1 (log_br_301).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t301 : ((-53598022699/1250000000000 : ℚ) : ℝ) ≤ stT323 301 := by
  have hc : ((-92989/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((301 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c301).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_301).2
  have h0 : (0:ℝ) ≤ ((301 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53598022699/1250000000000 : ℚ) : ℝ)
      = ((576391/10000000 : ℚ) : ℝ) * ((-92989/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c302 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-942993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -875721/1250000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 294
    (log_br_302).1 (log_br_302).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t302 : ((-135672415887/2500000000000 : ℚ) : ℝ) ≤ stT323 302 := by
  have hc : ((-943093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((302 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c302).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_302).2
  have h0 : (0:ℝ) ≤ ((302 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135672415887/2500000000000 : ℚ) : ℝ)
      = ((143859/2500000 : ℚ) : ℝ) * ((-943093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c303 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-163007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2168167/5000000) (δ := 2039/125000000) (ψ := 3441/250000) 323 294
    (log_br_303).1 (log_br_303).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t303 : ((-18740504979/2000000000000 : ℚ) : ℝ) ≤ stT323 303 := by
  have hc : ((-163107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((303 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c303).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_303).2
  have h0 : (0:ℝ) ≤ ((303 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18740504979/2000000000000 : ℚ) : ℝ)
      = ((114897/2000000 : ℚ) : ℝ) * ((-163107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c304 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((783647/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1675703/10000000) (δ := 16291/1000000000) (ψ := 3441/250000) 323 294
    (log_br_304).1 (log_br_304).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t304 : ((449394762833/10000000000000 : ℚ) : ℝ) ≤ stT323 304 := by
  have hc : ((783547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((304 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c304).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_304).1
  have hw2 : ((304 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((449394762833/10000000000000 : ℚ) : ℝ)
      = ((573539/10000000 : ℚ) : ℝ) * ((783547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c305 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((462369/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 976127/10000000) (δ := 16291/1000000000) (ψ := 3441/250000) 323 294
    (log_br_305).1 (log_br_305).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t305 : ((132361467381/2500000000000 : ℚ) : ℝ) ≤ stT323 305 := by
  have hc : ((462319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((305 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c305).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_305).1
  have hw2 : ((305 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((286299/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132361467381/2500000000000 : ℚ) : ℝ)
      = ((286299/5000000 : ℚ) : ℝ) * ((462319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c306 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((122727/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1809699/5000000) (δ := 4053/250000000) (ψ := 3441/250000) 323 294
    (log_br_306).1 (log_br_306).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t306 : ((70101073447/10000000000000 : ℚ) : ℝ) ≤ stT323 306 := by
  have hc : ((122627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((306 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c306).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_306).1
  have hw2 : ((306 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((571661/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70101073447/10000000000000 : ℚ) : ℝ)
      = ((571661/10000000 : ℚ) : ℝ) * ((122627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c307 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-802087/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6253947/10000000) (δ := 16291/1000000000) (ψ := 3441/250000) 323 294
    (log_br_307).1 (log_br_307).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t307 : ((-457832988697/10000000000000 : ℚ) : ℝ) ≤ stT323 307 := by
  have hc : ((-802187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((307 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c307).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_307).2
  have h0 : (0:ℝ) ≤ ((307 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-457832988697/10000000000000 : ℚ) : ℝ)
      = ((570731/10000000 : ℚ) : ℝ) * ((-802187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c308 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-114621/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3414013/5000000) (δ := 2023/125000000) (ψ := 3441/250000) 323 295
    (log_br_308).1 (log_br_308).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t308 : ((-130637024401/2500000000000 : ℚ) : ℝ) ≤ stT323 308 := by
  have hc : ((-229267/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((308 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c308).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_308).2
  have h0 : (0:ℝ) ≤ ((308 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130637024401/2500000000000 : ℚ) : ℝ)
      = ((569803/10000000 : ℚ) : ℝ) * ((-229267/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c309 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-113167/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -842103/2000000) (δ := 4071/250000000) (ψ := 3441/250000) 323 295
    (log_br_309).1 (log_br_309).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t309 : ((-64435444227/10000000000000 : ℚ) : ℝ) ≤ stT323 309 := by
  have hc : ((-113267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((309 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c309).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_309).2
  have h0 : (0:ℝ) ≤ ((309 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64435444227/10000000000000 : ℚ) : ℝ)
      = ((568881/10000000 : ℚ) : ℝ) * ((-113267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c310 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((400871/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -800741/5000000) (δ := 16219/1000000000) (ψ := 3441/250000) 323 295
    (log_br_310).1 (log_br_310).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t310 : ((227650695981/5000000000000 : ℚ) : ℝ) ≤ stT323 310 := by
  have hc : ((400821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((310 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c310).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_310).1
  have hw2 : ((310 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567961/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227650695981/5000000000000 : ℚ) : ℝ)
      = ((567961/10000000 : ℚ) : ℝ) * ((400821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c311 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((46059/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 999233/10000000) (δ := 2023/125000000) (ψ := 3441/250000) 323 295
    (log_br_311).1 (log_br_311).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t311 : ((13057391269/250000000000 : ℚ) : ℝ) ≤ stT323 311 := by
  have hc : ((23027/25000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((311 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c311).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_311).1
  have hw2 : ((311 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((567047/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13057391269/250000000000 : ℚ) : ℝ)
      = ((567047/10000000 : ℚ) : ℝ) * ((23027/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c312 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((66903/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 359147/1000000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 295
    (log_br_312).1 (log_br_312).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t312 : ((18924011857/2500000000000 : ℚ) : ℝ) ≤ stT323 312 := by
  have hc : ((66853/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((312 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c312).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_312).1
  have hw2 : ((312 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((283069/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18924011857/2500000000000 : ℚ) : ℝ)
      = ((283069/5000000 : ℚ) : ℝ) * ((66853/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c313 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-782949/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 617547/1000000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 295
    (log_br_313).1 (log_br_313).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t313 : ((-221302959233/5000000000000 : ℚ) : ℝ) ≤ stT323 313 := by
  have hc : ((-783049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((313 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c313).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_313).2
  have h0 : (0:ℝ) ≤ ((313 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-221302959233/5000000000000 : ℚ) : ℝ)
      = ((282617/5000000 : ℚ) : ℝ) * ((-783049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c314 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-234071/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -695673/1000000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 296
    (log_br_314).1 (log_br_314).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t314 : ((-8256756123/156250000000 : ℚ) : ℝ) ≤ stT323 314 := by
  have hc : ((-14631/15625 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((314 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c314).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_314).2
  have h0 : (0:ℝ) ≤ ((314 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8256756123/156250000000 : ℚ) : ℝ)
      = ((564333/10000000 : ℚ) : ℝ) * ((-14631/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c315 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-91901/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2194561/5000000) (δ := 16327/1000000000) (ψ := 3441/250000) 323 296
    (log_br_315).1 (log_br_315).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t315 : ((-51808595587/5000000000000 : ℚ) : ℝ) ≤ stT323 315 := by
  have hc : ((-91951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((315 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c315).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_315).2
  have h0 : (0:ℝ) ≤ ((315 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51808595587/5000000000000 : ℚ) : ℝ)
      = ((563437/10000000 : ℚ) : ℝ) * ((-91951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c316 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((743927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -182967/1000000) (δ := 16327/1000000000) (ψ := 3441/250000) 323 296
    (log_br_316).1 (log_br_316).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t316 : ((418434672061/10000000000000 : ℚ) : ℝ) ≤ stT323 316 := by
  have hc : ((743827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((316 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c316).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_316).1
  have hw2 : ((316 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((562543/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((418434672061/10000000000000 : ℚ) : ℝ)
      = ((562543/10000000 : ℚ) : ℝ) * ((743827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c317 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((958629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360813/5000000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 296
    (log_br_317).1 (log_br_317).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t317 : ((107672521099/2000000000000 : ℚ) : ℝ) ≤ stT323 317 := by
  have hc : ((958529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((317 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c317).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_317).1
  have hw2 : ((317 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((112331/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107672521099/2000000000000 : ℚ) : ℝ)
      = ((112331/2000000 : ℚ) : ℝ) * ((958529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c318 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((13087/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 102029/312500) (δ := 16227/1000000000) (ψ := 3441/250000) 323 296
    (log_br_318).1 (log_br_318).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t318 : ((917002413/62500000000 : ℚ) : ℝ) ≤ stT323 318 := by
  have hc : ((6541/25000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((318 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c318).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_318).1
  have hw2 : ((318 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((140193/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((917002413/62500000000 : ℚ) : ℝ)
      = ((140193/2500000 : ℚ) : ℝ) * ((6541/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c319 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-170287/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1450079/2500000) (δ := 4069/250000000) (ψ := 3441/250000) 323 296
    (log_br_319).1 (log_br_319).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t319 : ((-11919562077/312500000000 : ℚ) : ℝ) ≤ stT323 319 := by
  have hc : ((-21289/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((319 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c319).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_319).2
  have h0 : (0:ℝ) ≤ ((319 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11919562077/312500000000 : ℚ) : ℝ)
      = ((559893/10000000 : ℚ) : ℝ) * ((-21289/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c320 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-491053/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7380333/10000000) (δ := 8167/500000000) (ψ := 3441/250000) 323 297
    (log_br_320).1 (log_br_320).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t320 : ((-274534925751/5000000000000 : ℚ) : ℝ) ≤ stT323 320 := by
  have hc : ((-491103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((320 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c320).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_320).2
  have h0 : (0:ℝ) ≤ ((320 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-274534925751/5000000000000 : ℚ) : ℝ)
      = ((559017/10000000 : ℚ) : ℝ) * ((-491103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c321 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-45611/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1215193/2500000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 297
    (log_br_321).1 (log_br_321).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t321 : ((-25464574031/1250000000000 : ℚ) : ℝ) ≤ stT323 321 := by
  have hc : ((-91247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((321 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c321).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_321).2
  have h0 : (0:ℝ) ≤ ((321 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25464574031/1250000000000 : ℚ) : ℝ)
      = ((279073/5000000 : ℚ) : ℝ) * ((-91247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c322 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((590071/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -587281/2500000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 297
    (log_br_322).1 (log_br_322).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t322 : ((164388929469/5000000000000 : ℚ) : ℝ) ≤ stT323 322 := by
  have hc : ((589971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((322 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c322).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_322).1
  have hw2 : ((322 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278639/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164388929469/5000000000000 : ℚ) : ℝ)
      = ((278639/5000000 : ℚ) : ℝ) * ((589971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c323 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((249521/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38693/2500000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 297
    (log_br_323).1 (log_br_323).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t323 : ((8676441709/156250000000 : ℚ) : ℝ) ≤ stT323 323 := by
  have hc : ((31187/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((323 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c323).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_323).1
  have hw2 : ((323 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((278207/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8676441709/156250000000 : ℚ) : ℝ)
      = ((278207/5000000 : ℚ) : ℝ) * ((31187/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c324 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((61069/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 662729/2500000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 297
    (log_br_324).1 (log_br_324).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t324 : ((13568097543/500000000000 : ℚ) : ℝ) ≤ stT323 324 := by
  have hc : ((122113/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((324 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c324).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_324).1
  have hw2 : ((324 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((111111/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13568097543/500000000000 : ℚ) : ℝ)
      = ((111111/2000000 : ℚ) : ℝ) * ((122113/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c325 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-14567/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1284827/2500000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 297
    (log_br_325).1 (log_br_325).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t325 : ((-64656503261/2500000000000 : ℚ) : ℝ) ≤ stT323 325 := by
  have hc : ((-116561/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((325 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c325).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_325).2
  have h0 : (0:ℝ) ≤ ((325 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64656503261/2500000000000 : ℚ) : ℝ)
      = ((554701/10000000 : ℚ) : ℝ) * ((-116561/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c326 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-248907/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 762011/1000000) (δ := 8167/500000000) (ψ := 3441/250000) 323 297
    (log_br_326).1 (log_br_326).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t326 : ((-34467684817/625000000000 : ℚ) : ℝ) ≤ stT323 326 := by
  have hc : ((-62233/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((326 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c326).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_326).2
  have h0 : (0:ℝ) ≤ ((326 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34467684817/625000000000 : ℚ) : ℝ)
      = ((553849/10000000 : ℚ) : ℝ) * ((-62233/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c327 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-124989/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5614643/10000000) (δ := 8131/500000000) (ψ := 3441/250000) 323 298
    (log_br_327).1 (log_br_327).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t327 : ((-34565113509/1000000000000 : ℚ) : ℝ) ≤ stT323 327 := by
  have hc : ((-125009/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((327 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c327).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_327).2
  have h0 : (0:ℝ) ≤ ((327 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34565113509/1000000000000 : ℚ) : ℝ)
      = ((276501/5000000 : ℚ) : ℝ) * ((-125009/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c328 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((15311/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3148941/10000000) (δ := 16341/1000000000) (ψ := 3441/250000) 323 298
    (log_br_328).1 (log_br_328).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t328 : ((4225657521/250000000000 : ℚ) : ℝ) ≤ stT323 328 := by
  have hc : ((7653/25000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((328 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c328).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_328).1
  have hw2 : ((328 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((552157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4225657521/250000000000 : ℚ) : ℝ)
      = ((552157/10000000 : ℚ) : ℝ) * ((7653/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c329 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((962063/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690831/10000000) (δ := 8131/500000000) (ψ := 3441/250000) 323 298
    (log_br_329).1 (log_br_329).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t329 : ((530346555271/10000000000000 : ℚ) : ℝ) ≤ stT323 329 := by
  have hc : ((961963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((329 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c329).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_329).1
  have hw2 : ((329 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((551317/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((530346555271/10000000000000 : ℚ) : ℝ)
      = ((551317/10000000 : ℚ) : ℝ) * ((961963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c330 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((381149/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1759851/10000000) (δ := 8081/500000000) (ψ := 3441/250000) 323 298
    (log_br_330).1 (log_br_330).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t330 : ((209787758619/5000000000000 : ℚ) : ℝ) ≤ stT323 330 := by
  have hc : ((381099/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((330 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c330).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_330).1
  have hw2 : ((330 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((550481/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209787758619/5000000000000 : ℚ) : ℝ)
      = ((550481/10000000 : ℚ) : ℝ) * ((381099/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c331 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-110221/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 131347/312500) (δ := 16241/1000000000) (ψ := 3441/250000) 323 298
    (log_br_331).1 (log_br_331).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t331 : ((-1212758753/200000000000 : ℚ) : ℝ) ≤ stT323 331 := by
  have hc : ((-110321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((331 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c331).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_331).2
  have h0 : (0:ℝ) ≤ ((331 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1212758753/200000000000 : ℚ) : ℝ)
      = ((10993/200000 : ℚ) : ℝ) * ((-110321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c332 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-884213/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 207469/312500) (δ := 8131/500000000) (ψ := 3441/250000) 323 298
    (log_br_332).1 (log_br_332).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t332 : ((-242665214643/5000000000000 : ℚ) : ℝ) ≤ stT323 332 := by
  have hc : ((-884313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((332 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c332).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_332).2
  have h0 : (0:ℝ) ≤ ((332 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242665214643/5000000000000 : ℚ) : ℝ)
      = ((274411/5000000 : ℚ) : ℝ) * ((-884313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c333 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-884473/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6640399/10000000) (δ := 3251/200000000) (ψ := 3441/250000) 323 299
    (log_br_333).1 (log_br_333).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t333 : ((-484743350281/10000000000000 : ℚ) : ℝ) ≤ stT323 333 := by
  have hc : ((-884573/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((333 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c333).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_333).2
  have h0 : (0:ℝ) ≤ ((333 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484743350281/10000000000000 : ℚ) : ℝ)
      = ((547997/10000000 : ℚ) : ℝ) * ((-884573/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c334 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-58291/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421911/1000000) (δ := 3231/200000000) (ψ := 3441/250000) 323 299
    (log_br_334).1 (log_br_334).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t334 : ((-3990349377/625000000000 : ℚ) : ℝ) ≤ stT323 334 := by
  have hc : ((-58341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((334 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c334).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_334).2
  have h0 : (0:ℝ) ≤ ((334 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3990349377/625000000000 : ℚ) : ℝ)
      = ((68397/1250000 : ℚ) : ℝ) * ((-58341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c335 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((750483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -112813/625000) (δ := 3231/200000000) (ψ := 3441/250000) 323 299
    (log_br_335).1 (log_br_335).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t335 : ((204988877557/5000000000000 : ℚ) : ℝ) ≤ stT323 335 := by
  have hc : ((750383/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((335 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c335).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_335).1
  have hw2 : ((335 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((273179/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((204988877557/5000000000000 : ℚ) : ℝ)
      = ((273179/5000000 : ℚ) : ℝ) * ((750383/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c336 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((242791/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 601827/10000000) (δ := 4087/250000000) (ψ := 3441/250000) 323 299
    (log_br_336).1 (log_br_336).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t336 : ((8277470919/156250000000 : ℚ) : ℝ) ≤ stT323 336 := by
  have hc : ((121383/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((336 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c336).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_336).1
  have hw2 : ((336 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((68193/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8277470919/156250000000 : ℚ) : ℝ)
      = ((68193/1250000 : ℚ) : ℝ) * ((121383/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c337 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((180889/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 600311/2000000) (δ := 3231/200000000) (ψ := 3441/250000) 323 299
    (log_br_337).1 (log_br_337).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t337 : ((49254575913/2500000000000 : ℚ) : ℝ) ≤ stT323 337 := by
  have hc : ((180839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((337 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c337).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_337).1
  have hw2 : ((337 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((272367/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49254575913/2500000000000 : ℚ) : ℝ)
      = ((272367/5000000 : ℚ) : ℝ) * ((180839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c338 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-110747/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5394097/10000000) (δ := 2031/125000000) (ψ := 3441/250000) 323 299
    (log_br_338).1 (log_br_338).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t338 : ((-60249383543/2000000000000 : ℚ) : ℝ) ≤ stT323 338 := by
  have hc : ((-110767/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((338 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c338).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_338).2
  have h0 : (0:ℝ) ≤ ((338 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60249383543/2000000000000 : ℚ) : ℝ)
      = ((543929/10000000 : ℚ) : ℝ) * ((-110767/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c339 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-999559/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3889847/5000000) (δ := 3231/200000000) (ψ := 3441/250000) 323 299
    (log_br_339).1 (log_br_339).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t339 : ((-271470397017/5000000000000 : ℚ) : ℝ) ≤ stT323 339 := by
  have hc : ((-999659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((339 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c339).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_339).2
  have h0 : (0:ℝ) ≤ ((339 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271470397017/5000000000000 : ℚ) : ℝ)
      = ((271563/5000000 : ℚ) : ℝ) * ((-999659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c340 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-302241/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2774889/5000000) (δ := 3231/200000000) (ψ := 3441/250000) 323 300
    (log_br_340).1 (log_br_340).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t340 : ((-163940571157/5000000000000 : ℚ) : ℝ) ≤ stT323 340 := by
  have hc : ((-302291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((340 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c340).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_340).2
  have h0 : (0:ℝ) ≤ ((340 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163940571157/5000000000000 : ℚ) : ℝ)
      = ((542327/10000000 : ℚ) : ℝ) * ((-302291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c341 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((59003/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -397289/1250000) (δ := 3231/200000000) (ψ := 3441/250000) 323 300
    (log_br_341).1 (log_br_341).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t341 : ((3194106399/200000000000 : ℚ) : ℝ) ≤ stT323 341 := by
  have hc : ((58983/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((341 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c341).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_341).1
  have hw2 : ((341 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((54153/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3194106399/200000000000 : ℚ) : ℝ)
      = ((54153/1000000 : ℚ) : ℝ) * ((58983/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c342 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((118437/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -81371/1000000) (δ := 2031/125000000) (ψ := 3441/250000) 323 300
    (log_br_342).1 (log_br_342).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t342 : ((64036627281/1250000000000 : ℚ) : ℝ) ≤ stT323 342 := by
  have hc : ((236849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((342 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c342).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_342).1
  have hw2 : ((342 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((270369/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64036627281/1250000000000 : ℚ) : ℝ)
      = ((270369/5000000 : ℚ) : ℝ) * ((236849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c343 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((815283/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385987/2500000) (δ := 3231/200000000) (ψ := 3441/250000) 323 300
    (log_br_343).1 (log_br_343).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t343 : ((440157245667/10000000000000 : ℚ) : ℝ) ≤ stT323 343 := by
  have hc : ((815183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((343 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c343).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_343).1
  have hw2 : ((343 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539949/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((440157245667/10000000000000 : ℚ) : ℝ)
      = ((539949/10000000 : ℚ) : ℝ) * ((815183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c344 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((12899/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1947371/5000000) (δ := 3231/200000000) (ψ := 3441/250000) 323 300
    (log_br_344).1 (log_br_344).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t344 : ((6900747237/10000000000000 : ℚ) : ℝ) ≤ stT323 344 := by
  have hc : ((12799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((344 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c344).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_344).1
  have hw2 : ((344 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((539163/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6900747237/10000000000000 : ℚ) : ℝ)
      = ((539163/10000000 : ℚ) : ℝ) * ((12799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c345 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-798443/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6238753/10000000) (δ := 3231/200000000) (ψ := 3441/250000) 323 300
    (log_br_345).1 (log_br_345).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t345 : ((-214960588713/5000000000000 : ℚ) : ℝ) ≤ stT323 345 := by
  have hc : ((-798543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((345 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c345).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_345).2
  have h0 : (0:ℝ) ≤ ((345 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-214960588713/5000000000000 : ℚ) : ℝ)
      = ((269191/5000000 : ℚ) : ℝ) * ((-798543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c346 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-239649/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7132063/10000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 301
    (log_br_346).1 (log_br_346).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t346 : ((-16106212637/312500000000 : ℚ) : ℝ) ≤ stT323 346 := by
  have hc : ((-119837/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((346 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c346).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_346).2
  have h0 : (0:ℝ) ≤ ((346 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16106212637/312500000000 : ℚ) : ℝ)
      = ((134401/2500000 : ℚ) : ℝ) * ((-119837/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c347 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-171379/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2400809/5000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 301
    (log_br_347).1 (log_br_347).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t347 : ((-92028058641/5000000000000 : ℚ) : ℝ) ≤ stT323 347 := by
  have hc : ((-171429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((347 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c347).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_347).2
  have h0 : (0:ℝ) ≤ ((347 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92028058641/5000000000000 : ℚ) : ℝ)
      = ((536829/10000000 : ℚ) : ℝ) * ((-171429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c348 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((34233/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19823/80000) (δ := 16263/1000000000) (ψ := 3441/250000) 323 301
    (log_br_348).1 (log_br_348).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t348 : ((9173727349/312500000000 : ℚ) : ℝ) ≤ stT323 348 := by
  have hc : ((136907/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((348 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c348).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_348).1
  have hw2 : ((348 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9173727349/312500000000 : ℚ) : ℝ)
      = ((67007/1250000 : ℚ) : ℝ) * ((136907/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c349 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((997933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -80377/5000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 301
    (log_br_349).1 (log_br_349).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t349 : ((534127033071/10000000000000 : ℚ) : ℝ) ≤ stT323 349 := by
  have hc : ((997833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((349 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c349).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_349).1
  have hw2 : ((349 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((535287/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((534127033071/10000000000000 : ℚ) : ℝ)
      = ((535287/10000000 : ℚ) : ℝ) * ((997833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c350 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((652539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 429933/2000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 301
    (log_br_350).1 (log_br_350).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t350 : ((174371499579/5000000000000 : ℚ) : ℝ) ≤ stT323 350 := by
  have hc : ((652439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((350 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c350).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_350).1
  have hw2 : ((350 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((267261/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174371499579/5000000000000 : ℚ) : ℝ)
      = ((267261/5000000 : ℚ) : ℝ) * ((652439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c351 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-209067/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4453543/10000000) (δ := 203/12500000) (ψ := 3441/250000) 323 301
    (log_br_351).1 (log_br_351).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t351 : ((-111645187087/10000000000000 : ℚ) : ℝ) ≤ stT323 351 := by
  have hc : ((-209167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((351 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c351).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_351).2
  have h0 : (0:ℝ) ≤ ((351 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111645187087/10000000000000 : ℚ) : ℝ)
      = ((533761/10000000 : ℚ) : ℝ) * ((-209167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c352 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-904209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 16877/25000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 301
    (log_br_352).1 (log_br_352).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t352 : ((-240999252809/5000000000000 : ℚ) : ℝ) ≤ stT323 352 := by
  have hc : ((-904309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((352 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c352).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_352).2
  have h0 : (0:ℝ) ≤ ((352 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240999252809/5000000000000 : ℚ) : ℝ)
      = ((266501/5000000 : ℚ) : ℝ) * ((-904309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c353 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-111159/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6666367/10000000) (δ := 16333/1000000000) (ψ := 3441/250000) 323 302
    (log_br_353).1 (log_br_353).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t353 : ((-118341394721/2500000000000 : ℚ) : ℝ) ≤ stT323 353 := by
  have hc : ((-222343/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((353 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c353).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_353).2
  have h0 : (0:ℝ) ≤ ((353 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118341394721/2500000000000 : ℚ) : ℝ)
      = ((532247/10000000 : ℚ) : ℝ) * ((-222343/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c354 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-45253/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -438203/1000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 302
    (log_br_354).1 (log_br_354).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t354 : ((-2406503061/250000000000 : ℚ) : ℝ) ≤ stT323 354 := by
  have hc : ((-22639/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((354 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c354).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_354).2
  have h0 : (0:ℝ) ≤ ((354 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2406503061/250000000000 : ℚ) : ℝ)
      = ((106299/2000000 : ℚ) : ℝ) * ((-22639/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c355 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((666201/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1052117/5000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 302
    (log_br_355).1 (log_br_355).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t355 : ((44191138643/1250000000000 : ℚ) : ℝ) ≤ stT323 355 := by
  have hc : ((666101/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((355 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c355).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_355).1
  have hw2 : ((355 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66343/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44191138643/1250000000000 : ℚ) : ℝ)
      = ((66343/1250000 : ℚ) : ℝ) * ((666101/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c356 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((997763/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5227/312500) (δ := 1627/100000000) (ψ := 3441/250000) 323 302
    (log_br_356).1 (log_br_356).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t356 : ((264379697337/5000000000000 : ℚ) : ℝ) ≤ stT323 356 := by
  have hc : ((997663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((356 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c356).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_356).1
  have hw2 : ((356 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((264999/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264379697337/5000000000000 : ℚ) : ℝ)
      = ((264999/5000000 : ℚ) : ℝ) * ((997663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c357 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((70361/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2432301/10000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 302
    (log_br_357).1 (log_br_357).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t357 : ((9308091429/312500000000 : ℚ) : ℝ) ≤ stT323 357 := by
  have hc : ((140697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((357 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c357).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_357).1
  have hw2 : ((357 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66157/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9308091429/312500000000 : ℚ) : ℝ)
      = ((66157/1250000 : ℚ) : ℝ) * ((140697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c358 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-75221/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29319/62500) (δ := 16233/1000000000) (ψ := 3441/250000) 323 302
    (log_br_358).1 (log_br_358).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t358 : ((-19884395091/1250000000000 : ℚ) : ℝ) ≤ stT323 358 := by
  have hc : ((-37623/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((358 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c358).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_358).2
  have h0 : (0:ℝ) ≤ ((358 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19884395091/1250000000000 : ℚ) : ℝ)
      = ((528517/10000000 : ℚ) : ℝ) * ((-37623/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c359 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-934409/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6943481/10000000) (δ := 1627/100000000) (ψ := 3441/250000) 323 302
    (log_br_359).1 (log_br_359).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t359 : ((-24660758001/500000000000 : ℚ) : ℝ) ≤ stT323 359 := by
  have hc : ((-934509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((359 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c359).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_359).2
  have h0 : (0:ℝ) ≤ ((359 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24660758001/500000000000 : ℚ) : ℝ)
      = ((26389/500000 : ℚ) : ℝ) * ((-934509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c360 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-860631/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325913/500000) (δ := 8113/500000000) (ψ := 3441/250000) 323 303
    (log_br_360).1 (log_br_360).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t360 : ((-453645691357/10000000000000 : ℚ) : ℝ) ≤ stT323 360 := by
  have hc : ((-860731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((360 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c360).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_360).2
  have h0 : (0:ℝ) ≤ ((360 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-453645691357/10000000000000 : ℚ) : ℝ)
      = ((527047/10000000 : ℚ) : ℝ) * ((-860731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c361 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-35019/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -66849/156250) (δ := 8163/500000000) (ψ := 3441/250000) 323 303
    (log_br_361).1 (log_br_361).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t361 : ((-1152763619/156250000000 : ℚ) : ℝ) ≤ stT323 361 := by
  have hc : ((-8761/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((361 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c361).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_361).2
  have h0 : (0:ℝ) ≤ ((361 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1152763619/156250000000 : ℚ) : ℝ)
      = ((131579/2500000 : ℚ) : ℝ) * ((-8761/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c362 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((341907/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -511137/2500000) (δ := 16277/1000000000) (ψ := 3441/250000) 323 303
    (log_br_362).1 (log_br_362).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t362 : ((44918984229/1250000000000 : ℚ) : ℝ) ≤ stT323 362 := by
  have hc : ((341857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((362 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c362).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_362).1
  have hw2 : ((362 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((131397/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44918984229/1250000000000 : ℚ) : ℝ)
      = ((131397/2500000 : ℚ) : ℝ) * ((341857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c363 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((997321/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183021/10000000) (δ := 8113/500000000) (ψ := 3441/250000) 323 303
    (log_br_363).1 (log_br_363).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t363 : ((523404405723/10000000000000 : ℚ) : ℝ) ≤ stT323 363 := by
  have hc : ((997221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((363 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c363).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_363).1
  have hw2 : ((363 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((524863/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((523404405723/10000000000000 : ℚ) : ℝ)
      = ((524863/10000000 : ℚ) : ℝ) * ((997221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c364 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((28603/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1202227/5000000) (δ := 16277/1000000000) (ψ := 3441/250000) 323 303
    (log_br_364).1 (log_br_364).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t364 : ((3747353229/125000000000 : ℚ) : ℝ) ≤ stT323 364 := by
  have hc : ((14299/25000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((364 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c364).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_364).1
  have hw2 : ((364 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3747353229/125000000000 : ℚ) : ℝ)
      = ((262071/5000000 : ℚ) : ℝ) * ((14299/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c365 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-136801/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 461983/1000000) (δ := 16177/1000000000) (ψ := 3441/250000) 323 303
    (log_br_365).1 (log_br_365).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t365 : ((-2238471807/156250000000 : ℚ) : ℝ) ≤ stT323 365 := by
  have hc : ((-136851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((365 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c365).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_365).2
  have h0 : (0:ℝ) ≤ ((365 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2238471807/156250000000 : ℚ) : ℝ)
      = ((16357/312500 : ℚ) : ℝ) * ((-136851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c366 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-229287/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136583/200000) (δ := 16177/1000000000) (ψ := 3441/250000) 323 303
    (log_br_366).1 (log_br_366).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t366 : ((-1872866347/39062500000 : ℚ) : ℝ) ≤ stT323 366 := by
  have hc : ((-14332/15625 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((366 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c366).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_366).2
  have h0 : (0:ℝ) ≤ ((366 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1872866347/39062500000 : ℚ) : ℝ)
      = ((522709/10000000 : ℚ) : ℝ) * ((-14332/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c367 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-445473/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133511/200000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 304
    (log_br_367).1 (log_br_367).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t367 : ((-58140305977/1250000000000 : ℚ) : ℝ) ≤ stT323 367 := by
  have hc : ((-445523/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((367 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c367).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_367).2
  have h0 : (0:ℝ) ≤ ((367 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58140305977/1250000000000 : ℚ) : ℝ)
      = ((130499/2500000 : ℚ) : ℝ) * ((-445523/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c368 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-8749/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4478261/10000000) (δ := 4071/250000000) (ψ := 3441/250000) 323 304
    (log_br_368).1 (log_br_368).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t368 : ((-4562825111/400000000000 : ℚ) : ℝ) ≤ stT323 368 := by
  have hc : ((-8753/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((368 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c368).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_368).2
  have h0 : (0:ℝ) ≤ ((368 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4562825111/400000000000 : ℚ) : ℝ)
      = ((521287/10000000 : ℚ) : ℝ) * ((-8753/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c369 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((121993/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2286949/10000000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 304
    (log_br_369).1 (log_br_369).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t369 : ((63496582367/2000000000000 : ℚ) : ℝ) ≤ stT323 369 := by
  have hc : ((121973/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((369 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c369).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_369).1
  have hw2 : ((369 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((520579/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((63496582367/2000000000000 : ℚ) : ℝ)
      = ((520579/10000000 : ℚ) : ℝ) * ((121973/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c370 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((39967/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -101531/10000000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 304
    (log_br_370).1 (log_br_370).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t370 : ((166206117/3200000000 : ℚ) : ℝ) ≤ stT323 370 := by
  have hc : ((39963/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((370 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c370).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_370).1
  have hw2 : ((370 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((4159/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166206117/3200000000 : ℚ) : ℝ)
      = ((4159/80000 : ℚ) : ℝ) * ((39963/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c371 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((21063/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 259739/1250000) (δ := 2023/125000000) (ψ := 3441/250000) 323 304
    (log_br_371).1 (log_br_371).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t371 : ((43734958173/1250000000000 : ℚ) : ℝ) ≤ stT323 371 := by
  have hc : ((168479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((371 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c371).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_371).1
  have hw2 : ((371 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((259587/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43734958173/1250000000000 : ℚ) : ℝ)
      = ((259587/5000000 : ℚ) : ℝ) * ((168479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c372 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-25891/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212577/500000) (δ := 16319/1000000000) (ψ := 3441/250000) 323 304
    (log_br_372).1 (log_br_372).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t372 : ((-3358557909/500000000000 : ℚ) : ℝ) ≤ stT323 372 := by
  have hc : ((-25911/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((372 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c372).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_372).2
  have h0 : (0:ℝ) ≤ ((372 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3358557909/500000000000 : ℚ) : ℝ)
      = ((129619/2500000 : ℚ) : ℝ) * ((-25911/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c373 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-839817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1283871/2000000) (δ := 2023/125000000) (ψ := 3441/250000) 323 304
    (log_br_373).1 (log_br_373).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t373 : ((-434893064177/10000000000000 : ℚ) : ℝ) ≤ stT323 373 := by
  have hc : ((-839917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((373 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c373).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_373).2
  have h0 : (0:ℝ) ≤ ((373 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-434893064177/10000000000000 : ℚ) : ℝ)
      = ((517781/10000000 : ℚ) : ℝ) * ((-839917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c374 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-957981/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7126689/10000000) (δ := 2039/125000000) (ψ := 3441/250000) 323 305
    (log_br_374).1 (log_br_374).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t374 : ((-15481630879/312500000000 : ℚ) : ℝ) ≤ stT323 374 := by
  have hc : ((-958081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((374 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c374).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_374).2
  have h0 : (0:ℝ) ≤ ((374 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15481630879/312500000000 : ℚ) : ℝ)
      = ((16159/312500 : ℚ) : ℝ) * ((-958081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c375 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-5067/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4970421/10000000) (δ := 16291/1000000000) (ψ := 3441/250000) 323 305
    (log_br_375).1 (log_br_375).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t375 : ((-5234468327/250000000000 : ℚ) : ℝ) ≤ stT323 375 := by
  have hc : ((-20273/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((375 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c375).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_375).2
  have h0 : (0:ℝ) ≤ ((375 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5234468327/250000000000 : ℚ) : ℝ)
      = ((258199/5000000 : ℚ) : ℝ) * ((-20273/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c376 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((428479/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22031/78125) (δ := 16191/1000000000) (ψ := 3441/250000) 323 305
    (log_br_376).1 (log_br_376).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t376 : ((22091933409/1000000000000 : ℚ) : ℝ) ≤ stT323 376 := by
  have hc : ((428379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((376 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c376).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_376).1
  have hw2 : ((376 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51571/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22091933409/1000000000000 : ℚ) : ℝ)
      = ((51571/1000000 : ℚ) : ℝ) * ((428379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c377 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((30117/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -42203/625000) (δ := 16191/1000000000) (ψ := 3441/250000) 323 305
    (log_br_377).1 (log_br_377).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t377 : ((62037714343/1250000000000 : ℚ) : ℝ) ≤ stT323 377 := by
  have hc : ((240911/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((377 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c377).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_377).1
  have hw2 : ((377 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((257513/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62037714343/1250000000000 : ℚ) : ℝ)
      = ((257513/5000000 : ℚ) : ℝ) * ((240911/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c378 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((833421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1463819/10000000) (δ := 2039/125000000) (ψ := 3441/250000) 323 305
    (log_br_378).1 (log_br_378).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t378 : ((53576707053/1250000000000 : ℚ) : ℝ) ≤ stT323 378 := by
  have hc : ((833321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((378 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c378).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_378).1
  have hw2 : ((378 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((64293/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53576707053/1250000000000 : ℚ) : ℝ)
      = ((64293/1250000 : ℚ) : ℝ) * ((833321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c379 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((4109/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 719463/2000000) (δ := 4053/250000000) (ψ := 3441/250000) 323 305
    (log_br_379).1 (log_br_379).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t379 : ((3374470851/500000000000 : ℚ) : ℝ) ≤ stT323 379 := by
  have hc : ((32847/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((379 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c379).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_379).1
  have hw2 : ((379 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((102733/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3374470851/500000000000 : ℚ) : ℝ)
      = ((102733/2000000 : ℚ) : ℝ) * ((32847/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c380 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-658809/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2862539/5000000) (δ := 16291/1000000000) (ψ := 3441/250000) 323 305
    (log_br_380).1 (log_br_380).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t380 : ((-33801372791/1000000000000 : ℚ) : ℝ) ≤ stT323 380 := by
  have hc : ((-658909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((380 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c380).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_380).2
  have h0 : (0:ℝ) ≤ ((380 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33801372791/1000000000000 : ℚ) : ℝ)
      = ((51299/1000000 : ℚ) : ℝ) * ((-658909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c381 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-249999/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1961817/2500000) (δ := 2039/125000000) (ψ := 3441/250000) 323 305
    (log_br_381).1 (log_br_381).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t381 : ((-4002852987/78125000000 : ℚ) : ℝ) ≤ stT323 381 := by
  have hc : ((-31253/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((381 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c381).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_381).2
  have h0 : (0:ℝ) ≤ ((381 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4002852987/78125000000 : ℚ) : ℝ)
      = ((128079/2500000 : ℚ) : ℝ) * ((-31253/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c382 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-664483/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1148799/2000000) (δ := 8099/500000000) (ψ := 3441/250000) 323 306
    (log_br_382).1 (log_br_382).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t382 : ((-68006113807/2000000000000 : ℚ) : ℝ) ≤ stT323 382 := by
  have hc : ((-664583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((382 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c382).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_382).2
  have h0 : (0:ℝ) ≤ ((382 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68006113807/2000000000000 : ℚ) : ℝ)
      = ((102329/2000000 : ℚ) : ℝ) * ((-664583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c383 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((58673/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -908237/2500000) (δ := 3241/200000000) (ψ := 3441/250000) 323 306
    (log_br_383).1 (log_br_383).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t383 : ((29252877/4882812500 : ℚ) : ℝ) ≤ stT323 383 := by
  have hc : ((58623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((383 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c383).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_383).1
  have hw2 : ((383 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3992/78125 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29252877/4882812500 : ℚ) : ℝ)
      = ((3992/78125 : ℚ) : ℝ) * ((58623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c384 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((409559/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1527311/10000000) (δ := 3241/200000000) (ψ := 3441/250000) 323 306
    (log_br_384).1 (log_br_384).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t384 : ((20897653779/500000000000 : ℚ) : ℝ) ≤ stT323 384 := by
  have hc : ((409509/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((384 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c384).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_384).1
  have hw2 : ((384 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20897653779/500000000000 : ℚ) : ℝ)
      = ((51031/1000000 : ℚ) : ℝ) * ((409509/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c385 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((973863/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 114567/2000000) (δ := 3241/200000000) (ψ := 3441/250000) 323 306
    (log_br_385).1 (log_br_385).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t385 : ((496275391661/10000000000000 : ℚ) : ℝ) ≤ stT323 385 := by
  have hc : ((973763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((385 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c385).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_385).1
  have hw2 : ((385 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((509647/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((496275391661/10000000000000 : ℚ) : ℝ)
      = ((509647/10000000 : ℚ) : ℝ) * ((973763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c386 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((482757/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 266749/1000000) (δ := 3241/200000000) (ψ := 3441/250000) 323 306
    (log_br_386).1 (log_br_386).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t386 : ((122832827901/5000000000000 : ℚ) : ℝ) ≤ stT323 386 := by
  have hc : ((482657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((386 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c386).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_386).1
  have hw2 : ((386 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((254493/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122832827901/5000000000000 : ℚ) : ℝ)
      = ((254493/5000000 : ℚ) : ℝ) * ((482657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c387 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-162919/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 951347/2000000) (δ := 8099/500000000) (ψ := 3441/250000) 323 306
    (log_br_387).1 (log_br_387).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t387 : ((-82841868801/5000000000000 : ℚ) : ℝ) ≤ stT323 387 := by
  have hc : ((-162969/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((387 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c387).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_387).2
  have h0 : (0:ℝ) ≤ ((387 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82841868801/5000000000000 : ℚ) : ℝ)
      = ((508329/10000000 : ℚ) : ℝ) * ((-162969/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c388 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-918971/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136813/200000) (δ := 3241/200000000) (ψ := 3441/250000) 323 306
    (log_br_388).1 (log_br_388).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t388 : ((-233294225427/5000000000000 : ℚ) : ℝ) ≤ stT323 388 := by
  have hc : ((-919071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((388 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c388).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_388).2
  have h0 : (0:ℝ) ≤ ((388 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233294225427/5000000000000 : ℚ) : ℝ)
      = ((253837/5000000 : ℚ) : ℝ) * ((-919071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c389 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-910597/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -848601/1250000) (δ := 8103/500000000) (ψ := 3441/250000) 323 307
    (log_br_389).1 (log_br_389).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t389 : ((-461742503637/10000000000000 : ℚ) : ℝ) ≤ stT323 389 := by
  have hc : ((-910697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((389 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c389).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_389).2
  have h0 : (0:ℝ) ≤ ((389 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-461742503637/10000000000000 : ℚ) : ℝ)
      = ((507021/10000000 : ℚ) : ℝ) * ((-910697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c390 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-310251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4715633/10000000) (δ := 16297/1000000000) (ψ := 3441/250000) 323 307
    (log_br_390).1 (log_br_390).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t390 : ((-15715243587/1000000000000 : ℚ) : ℝ) ≤ stT323 390 := by
  have hc : ((-310351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((390 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c390).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_390).2
  have h0 : (0:ℝ) ≤ ((390 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15715243587/1000000000000 : ℚ) : ℝ)
      = ((50637/1000000 : ℚ) : ℝ) * ((-310351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c391 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((122411/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2647787/10000000) (δ := 16297/1000000000) (ψ := 3441/250000) 323 307
    (log_br_391).1 (log_br_391).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t391 : ((30946585153/1250000000000 : ℚ) : ℝ) ≤ stT323 391 := by
  have hc : ((61193/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((391 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c391).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_391).1
  have hw2 : ((391 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((505721/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30946585153/1250000000000 : ℚ) : ℝ)
      = ((505721/10000000 : ℚ) : ℝ) * ((61193/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c392 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((972729/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -585189/10000000) (δ := 8153/500000000) (ψ := 3441/250000) 323 307
    (log_br_392).1 (log_br_392).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t392 : ((122812891201/2500000000000 : ℚ) : ℝ) ≤ stT323 392 := by
  have hc : ((972629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((392 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c392).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_392).1
  have hw2 : ((392 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122812891201/2500000000000 : ℚ) : ℝ)
      = ((126269/2500000 : ℚ) : ℝ) * ((972629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c393 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((207893/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1472159/10000000) (δ := 16197/1000000000) (ψ := 3441/250000) 323 307
    (log_br_393).1 (log_br_393).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t393 : ((26213869711/625000000000 : ℚ) : ℝ) ≤ stT323 393 := by
  have hc : ((51967/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((393 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c393).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_393).1
  have hw2 : ((393 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((504433/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26213869711/625000000000 : ℚ) : ℝ)
      = ((504433/10000000 : ℚ) : ℝ) * ((51967/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c394 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((160397/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3524259/10000000) (δ := 8103/500000000) (ψ := 3441/250000) 323 307
    (log_br_394).1 (log_br_394).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t394 : ((5047271639/625000000000 : ℚ) : ℝ) ≤ stT323 394 := by
  have hc : ((160297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((394 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c394).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_394).1
  have hw2 : ((394 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31487/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5047271639/625000000000 : ℚ) : ℝ)
      = ((31487/625000 : ℚ) : ℝ) * ((160297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c395 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-611257/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 557111/1000000) (δ := 8103/500000000) (ψ := 3441/250000) 323 307
    (log_br_395).1 (log_br_395).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t395 : ((-61521466267/2000000000000 : ℚ) : ℝ) ≤ stT323 395 := by
  have hc : ((-611357/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((395 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c395).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_395).2
  have h0 : (0:ℝ) ≤ ((395 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61521466267/2000000000000 : ℚ) : ℝ)
      = ((100631/2000000 : ℚ) : ℝ) * ((-611357/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c396 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-995353/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3806437/5000000) (δ := 8153/500000000) (ψ := 3441/250000) 323 307
    (log_br_396).1 (log_br_396).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t396 : ((-500234046107/10000000000000 : ℚ) : ℝ) ≤ stT323 396 := by
  have hc : ((-995453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((396 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c396).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_396).2
  have h0 : (0:ℝ) ≤ ((396 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-500234046107/10000000000000 : ℚ) : ℝ)
      = ((502519/10000000 : ℚ) : ℝ) * ((-995453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c397 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-94127/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -242343/400000) (δ := 1629/100000000) (ψ := 3441/250000) 323 308
    (log_br_397).1 (log_br_397).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t397 : ((-47247297097/1250000000000 : ℚ) : ℝ) ≤ stT323 397 := by
  have hc : ((-188279/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((397 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c397).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_397).2
  have h0 : (0:ℝ) ≤ ((397 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47247297097/1250000000000 : ℚ) : ℝ)
      = ((250943/5000000 : ℚ) : ℝ) * ((-188279/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c398 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-40019/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2013533/5000000) (δ := 16213/1000000000) (ψ := 3441/250000) 323 308
    (log_br_398).1 (log_br_398).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t398 : ((-4021969869/2000000000000 : ℚ) : ℝ) ≤ stT323 398 := by
  have hc : ((-40119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((398 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c398).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_398).2
  have h0 : (0:ℝ) ≤ ((398 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4021969869/2000000000000 : ℚ) : ℝ)
      = ((100251/2000000 : ℚ) : ℝ) * ((-40119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c399 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((348249/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1000363/5000000) (δ := 1629/100000000) (ψ := 3441/250000) 323 308
    (log_br_399).1 (log_br_399).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t399 : ((87158736287/2500000000000 : ℚ) : ℝ) ≤ stT323 399 := by
  have hc : ((348199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((399 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c399).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_399).1
  have hw2 : ((399 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((250313/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87158736287/2500000000000 : ℚ) : ℝ)
      = ((250313/5000000 : ℚ) : ℝ) * ((348199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c400 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((499983/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1283/625000) (δ := 16313/1000000000) (ψ := 3441/250000) 323 308
    (log_br_400).1 (log_br_400).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t400 : ((499933/10000000 : ℚ) : ℝ) ≤ stT323 400 := by
  have hc : ((499933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((400 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c400).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_400).1
  have hw2 : ((400 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/20 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499933/10000000 : ℚ) : ℝ)
      = ((1/20 : ℚ) : ℝ) * ((499933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c401 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((2144/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1018387/5000000) (δ := 1629/100000000) (ψ := 3441/250000) 323 308
    (log_br_401).1 (log_br_401).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t401 : ((1070506089/31250000000 : ℚ) : ℝ) ≤ stT323 401 := by
  have hc : ((34299/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((401 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c401).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_401).1
  have hw2 : ((401 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((31211/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1070506089/31250000000 : ℚ) : ℝ)
      = ((31211/625000 : ℚ) : ℝ) * ((34299/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c402 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-24179/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2023967/5000000) (δ := 16213/1000000000) (ψ := 3441/250000) 323 308
    (log_br_402).1 (log_br_402).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t402 : ((-2416866979/1000000000000 : ℚ) : ℝ) ≤ stT323 402 := by
  have hc : ((-24229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((402 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c402).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_402).2
  have h0 : (0:ℝ) ≤ ((402 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2416866979/1000000000000 : ℚ) : ℝ)
      = ((99751/2000000 : ℚ) : ℝ) * ((-24229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c403 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-150371/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 756771/1250000) (δ := 16313/1000000000) (ψ := 3441/250000) 323 308
    (log_br_403).1 (log_br_403).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t403 : ((-9364396397/250000000000 : ℚ) : ℝ) ≤ stT323 403 := by
  have hc : ((-150391/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((403 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c403).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_403).2
  have h0 : (0:ℝ) ≤ ((403 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9364396397/250000000000 : ℚ) : ℝ)
      = ((62267/1250000 : ℚ) : ℝ) * ((-150391/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c404 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-249189/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -956571/1250000) (δ := 51/3125000) (ψ := 3441/250000) 323 309
    (log_br_404).1 (log_br_404).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t404 : ((-61994350033/1250000000000 : ℚ) : ℝ) ≤ stT323 404 := by
  have hc : ((-124607/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((404 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c404).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_404).2
  have h0 : (0:ℝ) ≤ ((404 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61994350033/1250000000000 : ℚ) : ℝ)
      = ((497519/10000000 : ℚ) : ℝ) * ((-124607/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c405 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-127571/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5656267/10000000) (δ := 16183/1000000000) (ψ := 3441/250000) 323 309
    (log_br_405).1 (log_br_405).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t405 : ((-7925059783/250000000000 : ℚ) : ℝ) ≤ stT323 405 := by
  have hc : ((-127591/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((405 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c405).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_405).2
  have h0 : (0:ℝ) ≤ ((405 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7925059783/250000000000 : ℚ) : ℝ)
      = ((62113/1250000 : ℚ) : ℝ) * ((-127591/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c406 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((13081/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3664891/10000000) (δ := 811/50000000) (ψ := 3441/250000) 323 309
    (log_br_406).1 (log_br_406).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t406 : ((12971557867/2500000000000 : ℚ) : ℝ) ≤ stT323 406 := by
  have hc : ((26137/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((406 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c406).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_406).1
  have hw2 : ((406 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((496291/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12971557867/2500000000000 : ℚ) : ℝ)
      = ((496291/10000000 : ℚ) : ℝ) * ((26137/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c407 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((391483/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1678441/10000000) (δ := 811/50000000) (ψ := 3441/250000) 323 309
    (log_br_407).1 (log_br_407).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t407 : ((194025900873/5000000000000 : ℚ) : ℝ) ≤ stT323 407 := by
  have hc : ((391433/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((407 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c407).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_407).1
  have hw2 : ((407 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495681/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194025900873/5000000000000 : ℚ) : ℝ)
      = ((495681/10000000 : ℚ) : ℝ) * ((391433/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c408 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((62041/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75791/2500000) (δ := 811/50000000) (ψ := 3441/250000) 323 309
    (log_br_408).1 (log_br_408).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t408 : ((122846919147/2500000000000 : ℚ) : ℝ) ≤ stT323 408 := by
  have hc : ((248139/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((408 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c408).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_408).1
  have hw2 : ((408 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((495073/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122846919147/2500000000000 : ℚ) : ℝ)
      = ((495073/10000000 : ℚ) : ℝ) * ((248139/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c409 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((61219/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 569981/2500000) (δ := 811/50000000) (ψ := 3441/250000) 323 309
    (log_br_409).1 (log_br_409).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t409 : ((7566472953/250000000000 : ℚ) : ℝ) ≤ stT323 409 := by
  have hc : ((61209/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((409 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c409).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_409).1
  have hw2 : ((409 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((123617/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7566472953/250000000000 : ℚ) : ℝ)
      = ((123617/2500000 : ℚ) : ℝ) * ((61209/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c410 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-64787/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4251839/10000000) (δ := 811/50000000) (ψ := 3441/250000) 323 309
    (log_br_410).1 (log_br_410).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t410 : ((-6404145001/1000000000000 : ℚ) : ℝ) ≤ stT323 410 := by
  have hc : ((-64837/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((410 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c410).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_410).2
  have h0 : (0:ℝ) ≤ ((410 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6404145001/1000000000000 : ℚ) : ℝ)
      = ((98773/2000000 : ℚ) : ℝ) * ((-64837/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c411 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-793659/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 621899/1000000) (δ := 51/3125000) (ψ := 3441/250000) 323 309
    (log_br_411).1 (log_br_411).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t411 : ((-24470796211/625000000000 : ℚ) : ℝ) ≤ stT323 411 := by
  have hc : ((-793759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((411 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c411).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_411).2
  have h0 : (0:ℝ) ≤ ((411 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24470796211/625000000000 : ℚ) : ℝ)
      = ((30829/625000 : ℚ) : ℝ) * ((-793759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c412 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-991441/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1881667/2500000) (δ := 1011/62500000) (ψ := 3441/250000) 323 310
    (log_br_412).1 (log_br_412).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t412 : ((-97699509353/2000000000000 : ℚ) : ℝ) ≤ stT323 412 := by
  have hc : ((-991541/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((412 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c412).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_412).2
  have h0 : (0:ℝ) ≤ ((412 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97699509353/2000000000000 : ℚ) : ℝ)
      = ((98533/2000000 : ℚ) : ℝ) * ((-991541/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c413 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-610629/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2784563/5000000) (δ := 16327/1000000000) (ψ := 3441/250000) 323 310
    (log_br_413).1 (log_br_413).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t413 : ((-75130049393/2500000000000 : ℚ) : ℝ) ≤ stT323 413 := by
  have hc : ((-610729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((413 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c413).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_413).2
  have h0 : (0:ℝ) ≤ ((413 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75130049393/2500000000000 : ℚ) : ℝ)
      = ((123017/2500000 : ℚ) : ℝ) * ((-610729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c414 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((123969/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -904067/2500000) (δ := 16327/1000000000) (ψ := 3441/250000) 323 310
    (log_br_414).1 (log_br_414).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t414 : ((60878269037/10000000000000 : ℚ) : ℝ) ≤ stT323 414 := by
  have hc : ((123869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((414 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c414).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_414).1
  have hw2 : ((414 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((491473/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60878269037/10000000000000 : ℚ) : ℝ)
      = ((491473/10000000 : ℚ) : ℝ) * ((123869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c415 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((392767/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834047/5000000) (δ := 1011/62500000) (ψ := 3441/250000) 323 310
    (log_br_415).1 (log_br_415).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t415 : ((301213939/7812500000 : ℚ) : ℝ) ≤ stT323 415 := by
  have hc : ((392717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((415 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c415).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_415).1
  have hw2 : ((415 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((767/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301213939/7812500000 : ℚ) : ℝ)
      = ((767/15625 : ℚ) : ℝ) * ((392717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c416 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((496971/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 68829/2500000) (δ := 4069/250000000) (ψ := 3441/250000) 323 310
    (log_br_416).1 (log_br_416).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t416 : ((24363539709/500000000000 : ℚ) : ℝ) ≤ stT323 416 := by
  have hc : ((496921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((416 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c416).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_416).1
  have hw2 : ((416 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24363539709/500000000000 : ℚ) : ℝ)
      = ((49029/1000000 : ℚ) : ℝ) * ((496921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c417 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((632787/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 553531/2500000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 310
    (log_br_417).1 (log_br_417).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t417 : ((154914044637/5000000000000 : ℚ) : ℝ) ≤ stT323 417 := by
  have hc : ((632687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((417 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c417).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_417).1
  have hw2 : ((417 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((244851/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((154914044637/5000000000000 : ℚ) : ℝ)
      = ((244851/5000000 : ℚ) : ℝ) * ((632687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c418 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-88387/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 518531/1250000) (δ := 16227/1000000000) (ψ := 3441/250000) 323 310
    (log_br_418).1 (log_br_418).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t418 : ((-10820101873/2500000000000 : ℚ) : ℝ) ≤ stT323 418 := by
  have hc : ((-88487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((418 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c418).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_418).2
  have h0 : (0:ℝ) ≤ ((418 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10820101873/2500000000000 : ℚ) : ℝ)
      = ((122279/2500000 : ℚ) : ℝ) * ((-88487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c419 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-379023/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6077769/10000000) (δ := 1011/62500000) (ψ := 3441/250000) 323 310
    (log_br_419).1 (log_br_419).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t419 : ((-46297322709/1250000000000 : ℚ) : ℝ) ≤ stT323 419 := by
  have hc : ((-379073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((419 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c419).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_419).2
  have h0 : (0:ℝ) ≤ ((419 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46297322709/1250000000000 : ℚ) : ℝ)
      = ((122133/2500000 : ℚ) : ℝ) * ((-379073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c420 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-998231/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1926319/2500000) (δ := 16269/1000000000) (ψ := 3441/250000) 323 311
    (log_br_420).1 (log_br_420).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t420 : ((-487136609781/10000000000000 : ℚ) : ℝ) ≤ stT323 420 := by
  have hc : ((-998331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((420 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c420).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_420).2
  have h0 : (0:ℝ) ≤ ((420 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-487136609781/10000000000000 : ℚ) : ℝ)
      = ((487951/10000000 : ℚ) : ℝ) * ((-998331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c421 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-338319/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9039/15625) (δ := 16169/1000000000) (ψ := 3441/250000) 323 311
    (log_br_421).1 (log_br_421).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t421 : ((-164911237899/5000000000000 : ℚ) : ℝ) ≤ stT323 421 := by
  have hc : ((-338369/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((421 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c421).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_421).2
  have h0 : (0:ℝ) ≤ ((421 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164911237899/5000000000000 : ℚ) : ℝ)
      = ((487371/10000000 : ℚ) : ℝ) * ((-338369/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c422 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((2891/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1934583/5000000) (δ := 8117/500000000) (ψ := 3441/250000) 323 311
    (log_br_422).1 (log_br_422).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t422 : ((350307693/312500000000 : ℚ) : ℝ) ≤ stT323 422 := by
  have hc : ((5757/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((422 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c422).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_422).1
  have hw2 : ((422 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60849/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((350307693/312500000000 : ℚ) : ℝ)
      = ((60849/1250000 : ℚ) : ℝ) * ((5757/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c423 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((354333/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78319/400000) (δ := 8117/500000000) (ψ := 3441/250000) 323 311
    (log_br_423).1 (log_br_423).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t423 : ((21532257891/625000000000 : ℚ) : ℝ) ≤ stT323 423 := by
  have hc : ((354283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((423 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c423).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_423).1
  have hw2 : ((423 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60777/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21532257891/625000000000 : ℚ) : ℝ)
      = ((60777/1250000 : ℚ) : ℝ) * ((354283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c424 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((99979/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2049/400000) (δ := 8167/500000000) (ψ := 3441/250000) 323 311
    (log_br_424).1 (log_br_424).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t424 : ((24274572549/500000000000 : ℚ) : ℝ) ≤ stT323 424 := by
  have hc : ((99969/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((424 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c424).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_424).1
  have hw2 : ((424 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((242821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24274572549/500000000000 : ℚ) : ℝ)
      = ((242821/5000000 : ℚ) : ℝ) * ((99969/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c425 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((369099/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 925501/5000000) (δ := 16269/1000000000) (ψ := 3441/250000) 323 311
    (log_br_425).1 (log_br_425).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t425 : ((179014967479/5000000000000 : ℚ) : ℝ) ≤ stT323 425 := by
  have hc : ((369049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((425 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c425).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_425).1
  have hw2 : ((425 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((485071/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((179014967479/5000000000000 : ℚ) : ℝ)
      = ((485071/10000000 : ℚ) : ℝ) * ((369049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c426 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((3561/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3748789/10000000) (δ := 8117/500000000) (ψ := 3441/250000) 323 311
    (log_br_426).1 (log_br_426).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t426 : ((430721389/125000000000 : ℚ) : ℝ) ≤ stT323 426 := by
  have hc : ((889/12500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((426 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c426).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_426).1
  have hw2 : ((426 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((484501/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430721389/125000000000 : ℚ) : ℝ)
      = ((484501/10000000 : ℚ) : ℝ) * ((889/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c427 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-633491/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2821067/5000000) (δ := 16169/1000000000) (ψ := 3441/250000) 323 311
    (log_br_427).1 (log_br_427).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t427 : ((-153308113497/5000000000000 : ℚ) : ℝ) ≤ stT323 427 := by
  have hc : ((-633591/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((427 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c427).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_427).2
  have h0 : (0:ℝ) ≤ ((427 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-153308113497/5000000000000 : ℚ) : ℝ)
      = ((241967/5000000 : ℚ) : ℝ) * ((-633591/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c428 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-61979/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7530957/10000000) (δ := 16269/1000000000) (ψ := 3441/250000) 323 311
    (log_br_428).1 (log_br_428).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t428 : ((-119846993229/2500000000000 : ℚ) : ℝ) ≤ stT323 428 := by
  have hc : ((-247941/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((428 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c428).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_428).2
  have h0 : (0:ℝ) ≤ ((428 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119846993229/2500000000000 : ℚ) : ℝ)
      = ((483369/10000000 : ℚ) : ℝ) * ((-247941/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c429 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-811193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3146231/5000000) (δ := 8171/500000000) (ψ := 3441/250000) 323 312
    (log_br_429).1 (log_br_429).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t429 : ((-78339263373/2000000000000 : ℚ) : ℝ) ≤ stT323 429 := by
  have hc : ((-811293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((429 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c429).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_429).2
  have h0 : (0:ℝ) ≤ ((429 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-78339263373/2000000000000 : ℚ) : ℝ)
      = ((96561/2000000 : ℚ) : ℝ) * ((-811293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c430 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-19293/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110309/250000) (δ := 8121/500000000) (ψ := 3441/250000) 323 312
    (log_br_430).1 (log_br_430).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t430 : ((-9308736629/1000000000000 : ℚ) : ℝ) ≤ stT323 430 := by
  have hc : ((-19303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((430 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c430).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_430).2
  have h0 : (0:ℝ) ≤ ((430 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9308736629/1000000000000 : ℚ) : ℝ)
      = ((482243/10000000 : ℚ) : ℝ) * ((-19303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c431 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((131973/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2536699/10000000) (δ := 8121/500000000) (ψ := 3441/250000) 323 312
    (log_br_431).1 (log_br_431).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t431 : ((15889277121/625000000000 : ℚ) : ℝ) ≤ stT323 431 := by
  have hc : ((32987/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((431 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c431).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_431).1
  have hw2 : ((431 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((481683/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15889277121/625000000000 : ℚ) : ℝ)
      = ((481683/10000000 : ℚ) : ℝ) * ((32987/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c432 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((964797/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -332659/5000000) (δ := 16161/1000000000) (ψ := 3441/250000) 323 312
    (log_br_432).1 (log_br_432).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t432 : ((3713118753/80000000000 : ℚ) : ℝ) ≤ stT323 432 := by
  have hc : ((964697/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((432 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c432).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_432).1
  have hw2 : ((432 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3713118753/80000000000 : ℚ) : ℝ)
      = ((3849/80000 : ℚ) : ℝ) * ((964697/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c433 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((177333/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150223/1250000) (δ := 8171/500000000) (ψ := 3441/250000) 323 312
    (log_br_433).1 (log_br_433).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t433 : ((85211131097/2000000000000 : ℚ) : ℝ) ≤ stT323 433 := by
  have hc : ((177313/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((433 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c433).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_433).1
  have hw2 : ((433 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((480569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85211131097/2000000000000 : ℚ) : ℝ)
      = ((480569/10000000 : ℚ) : ℝ) * ((177313/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c434 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((42273/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122581/400000) (δ := 8171/500000000) (ψ := 3441/250000) 323 312
    (log_br_434).1 (log_br_434).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t434 : ((8114269563/500000000000 : ℚ) : ℝ) ≤ stT323 434 := by
  have hc : ((84521/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((434 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c434).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_434).1
  have hw2 : ((434 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((96003/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8114269563/500000000000 : ℚ) : ℝ)
      = ((96003/2000000 : ℚ) : ℝ) * ((84521/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c435 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-193971/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2461493/5000000) (δ := 8121/500000000) (ψ := 3441/250000) 323 312
    (log_br_435).1 (log_br_435).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t435 : ((-11628260593/625000000000 : ℚ) : ℝ) ≤ stT323 435 := by
  have hc : ((-194021/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((435 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c435).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_435).2
  have h0 : (0:ℝ) ≤ ((435 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11628260593/625000000000 : ℚ) : ℝ)
      = ((59933/1250000 : ℚ) : ℝ) * ((-194021/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c436 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-908663/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6777167/10000000) (δ := 16261/1000000000) (ψ := 3441/250000) 323 312
    (log_br_436).1 (log_br_436).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t436 : ((-217609661691/5000000000000 : ℚ) : ℝ) ≤ stT323 436 := by
  have hc : ((-908763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((436 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c436).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_436).2
  have h0 : (0:ℝ) ≤ ((436 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-217609661691/5000000000000 : ℚ) : ℝ)
      = ((239457/5000000 : ℚ) : ℝ) * ((-908763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c437 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-952567/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3540447/5000000) (δ := 16249/1000000000) (ψ := 3441/250000) 323 313
    (log_br_437).1 (log_br_437).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t437 : ((-91144509891/2000000000000 : ℚ) : ℝ) ≤ stT323 437 := by
  have hc : ((-952667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((437 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c437).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_437).2
  have h0 : (0:ℝ) ≤ ((437 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-91144509891/2000000000000 : ℚ) : ℝ)
      = ((95673/2000000 : ℚ) : ℝ) * ((-952667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c438 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-31231/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5235111/10000000) (δ := 8127/500000000) (ψ := 3441/250000) 323 313
    (log_br_438).1 (log_br_438).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t438 : ((-59703006231/2500000000000 : ℚ) : ℝ) ≤ stT323 438 := by
  have hc : ((-124949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((438 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c438).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_438).2
  have h0 : (0:ℝ) ≤ ((438 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59703006231/2500000000000 : ℚ) : ℝ)
      = ((477819/10000000 : ℚ) : ℝ) * ((-124949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c439 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((211739/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3393607/10000000) (δ := 8077/500000000) (ψ := 3441/250000) 323 313
    (log_br_439).1 (log_br_439).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t439 : ((101009580447/10000000000000 : ℚ) : ℝ) ≤ stT323 439 := by
  have hc : ((211639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((439 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c439).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_439).1
  have hw2 : ((439 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((477273/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101009580447/10000000000000 : ℚ) : ℝ)
      = ((477273/10000000 : ℚ) : ℝ) * ((211639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c440 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((812411/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -778151/5000000) (δ := 16249/1000000000) (ψ := 3441/250000) 323 313
    (log_br_440).1 (log_br_440).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t440 : ((387253835341/10000000000000 : ℚ) : ℝ) ≤ stT323 440 := by
  have hc : ((812311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((440 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c440).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_440).1
  have hw2 : ((440 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387253835341/10000000000000 : ℚ) : ℝ)
      = ((476731/10000000 : ℚ) : ℝ) * ((812311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c441 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((993877/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69201/2500000) (δ := 16349/1000000000) (ψ := 3441/250000) 323 313
    (log_br_441).1 (log_br_441).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t441 : ((47322666963/1000000000000 : ℚ) : ℝ) ≤ stT323 441 := by
  have hc : ((993777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((441 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c441).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_441).1
  have hw2 : ((441 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((47619/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47322666963/1000000000000 : ℚ) : ℝ)
      = ((47619/1000000 : ℚ) : ℝ) * ((993777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c442 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((83217/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2105791/10000000) (δ := 8077/500000000) (ψ := 3441/250000) 323 313
    (log_br_442).1 (log_br_442).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t442 : ((79152607259/2500000000000 : ℚ) : ℝ) ≤ stT323 442 := by
  have hc : ((166409/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((442 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c442).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_442).1
  have hw2 : ((442 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((475651/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79152607259/2500000000000 : ℚ) : ℝ)
      = ((475651/10000000 : ℚ) : ℝ) * ((166409/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c443 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-367/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196533/500000) (δ := 8127/500000000) (ψ := 3441/250000) 323 313
    (log_br_443).1 (log_br_443).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t443 : ((-4656127/62500000000 : ℚ) : ℝ) ≤ stT323 443 := by
  have hc : ((-49/31250 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((443 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c443).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_443).2
  have h0 : (0:ℝ) ≤ ((443 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4656127/62500000000 : ℚ) : ℝ)
      = ((95023/2000000 : ℚ) : ℝ) * ((-49/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c444 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-666697/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5751411/10000000) (δ := 8127/500000000) (ψ := 3441/250000) 323 313
    (log_br_444).1 (log_br_444).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t444 : ((-316447853463/10000000000000 : ℚ) : ℝ) ≤ stT323 444 := by
  have hc : ((-666797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((444 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c444).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_444).2
  have h0 : (0:ℝ) ≤ ((444 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316447853463/10000000000000 : ℚ) : ℝ)
      = ((474579/10000000 : ℚ) : ℝ) * ((-666797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c445 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-496733/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1892011/2500000) (δ := 8077/500000000) (ψ := 3441/250000) 323 313
    (log_br_445).1 (log_br_445).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t445 : ((-117748997009/2500000000000 : ℚ) : ℝ) ≤ stT323 445 := by
  have hc : ((-496783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((445 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c445).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_445).2
  have h0 : (0:ℝ) ≤ ((445 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117748997009/2500000000000 : ℚ) : ℝ)
      = ((237023/5000000 : ℚ) : ℝ) * ((-496783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c446 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-204817/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1581831/2500000) (δ := 4039/250000000) (ψ := 3441/250000) 323 314
    (log_br_446).1 (log_br_446).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t446 : ((-24248888697/625000000000 : ℚ) : ℝ) ≤ stT323 446 := by
  have hc : ((-102421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((446 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c446).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_446).2
  have h0 : (0:ℝ) ≤ ((446 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24248888697/625000000000 : ℚ) : ℝ)
      = ((236757/5000000 : ℚ) : ℝ) * ((-102421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c447 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-234537/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4518847/10000000) (δ := 4039/250000000) (ψ := 3441/250000) 323 314
    (log_br_447).1 (log_br_447).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t447 : ((-13872443351/1250000000000 : ℚ) : ℝ) ≤ stT323 447 := by
  have hc : ((-234637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((447 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c447).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_447).2
  have h0 : (0:ℝ) ≤ ((447 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13872443351/1250000000000 : ℚ) : ℝ)
      = ((59123/1250000 : ℚ) : ℝ) * ((-234637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c448 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((233133/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2714327/10000000) (δ := 16247/1000000000) (ψ := 3441/250000) 323 314
    (log_br_448).1 (log_br_448).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t448 : ((22024245753/1000000000000 : ℚ) : ℝ) ≤ stT323 448 := by
  have hc : ((233083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((448 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c448).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_448).1
  have hw2 : ((448 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22024245753/1000000000000 : ℚ) : ℝ)
      = ((94491/2000000 : ℚ) : ℝ) * ((233083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c449 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((5837/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36557/400000) (δ := 16247/1000000000) (ψ := 3441/250000) 323 314
    (log_br_449).1 (log_br_449).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t449 : ((22034836939/500000000000 : ℚ) : ℝ) ≤ stT323 449 := by
  have hc : ((46691/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((449 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c449).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_449).1
  have hw2 : ((449 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((471929/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22034836939/500000000000 : ℚ) : ℝ)
      = ((471929/10000000 : ℚ) : ℝ) * ((46691/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c450 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((938337/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 22063/250000) (δ := 16347/1000000000) (ψ := 3441/250000) 323 314
    (log_br_450).1 (log_br_450).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t450 : ((110572168687/2500000000000 : ℚ) : ℝ) ≤ stT323 450 := by
  have hc : ((938237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((450 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c450).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_450).1
  have hw2 : ((450 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((117851/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110572168687/2500000000000 : ℚ) : ℝ)
      = ((117851/2500000 : ℚ) : ℝ) * ((938237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c451 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((480121/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2675009/10000000) (δ := 4039/250000000) (ψ := 3441/250000) 323 314
    (log_br_451).1 (log_br_451).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t451 : ((226032768501/10000000000000 : ℚ) : ℝ) ≤ stT323 451 := by
  have hc : ((480021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((451 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c451).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_451).1
  have hw2 : ((451 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((470881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226032768501/10000000000000 : ℚ) : ℝ)
      = ((470881/10000000 : ℚ) : ℝ) * ((480021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c452 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-42589/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223173/500000) (δ := 4039/250000000) (ψ := 3441/250000) 323 314
    (log_br_452).1 (log_br_452).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t452 : ((-20041611849/2000000000000 : ℚ) : ℝ) ≤ stT323 452 := by
  have hc : ((-42609/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((452 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c452).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_452).2
  have h0 : (0:ℝ) ≤ ((452 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20041611849/2000000000000 : ℚ) : ℝ)
      = ((470361/10000000 : ℚ) : ℝ) * ((-42609/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c453 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-800673/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1249607/2000000) (δ := 4039/250000000) (ψ := 3441/250000) 323 314
    (log_br_453).1 (log_br_453).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t453 : ((-376235987093/10000000000000 : ℚ) : ℝ) ≤ stT323 453 := by
  have hc : ((-800773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((453 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c453).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_453).2
  have h0 : (0:ℝ) ≤ ((453 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376235987093/10000000000000 : ℚ) : ℝ)
      = ((469841/10000000 : ℚ) : ℝ) * ((-800773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c454 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-498781/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7679391/10000000) (δ := 203/12500000) (ψ := 3441/250000) 323 315
    (log_br_454).1 (log_br_454).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t454 : ((-58528340061/1250000000000 : ℚ) : ℝ) ≤ stT323 454 := by
  have hc : ((-498831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((454 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c454).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_454).2
  have h0 : (0:ℝ) ≤ ((454 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-58528340061/1250000000000 : ℚ) : ℝ)
      = ((117331/2500000 : ℚ) : ℝ) * ((-498831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c455 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-710539/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5902649/10000000) (δ := 817/50000000) (ψ := 3441/250000) 323 315
    (log_br_455).1 (log_br_455).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t455 : ((-41644156039/1250000000000 : ℚ) : ℝ) ≤ stT323 455 := by
  have hc : ((-710639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((455 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c455).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_455).2
  have h0 : (0:ℝ) ≤ ((455 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41644156039/1250000000000 : ℚ) : ℝ)
      = ((58601/1250000 : ℚ) : ℝ) * ((-710639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c456 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-4053/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4129863/10000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 315
    (log_br_456).1 (log_br_456).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t456 : ((-950166497/250000000000 : ℚ) : ℝ) ≤ stT323 456 := by
  have hc : ((-2029/25000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((456 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c456).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_456).2
  have h0 : (0:ℝ) ≤ ((456 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-950166497/250000000000 : ℚ) : ℝ)
      = ((468293/10000000 : ℚ) : ℝ) * ((-2029/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c457 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((293109/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1180517/5000000) (δ := 16263/1000000000) (ψ := 3441/250000) 323 315
    (log_br_457).1 (log_br_457).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t457 : ((6854356951/250000000000 : ℚ) : ℝ) ≤ stT323 457 := by
  have hc : ((293059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((457 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c457).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_457).1
  have hw2 : ((457 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((23389/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6854356951/250000000000 : ℚ) : ℝ)
      = ((23389/500000 : ℚ) : ℝ) * ((293059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c458 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((971717/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -596001/10000000) (δ := 203/12500000) (ψ := 3441/250000) 323 315
    (log_br_458).1 (log_br_458).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t458 : ((454006503973/10000000000000 : ℚ) : ℝ) ≤ stT323 458 := by
  have hc : ((971617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((458 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c458).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_458).1
  have hw2 : ((458 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((467269/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((454006503973/10000000000000 : ℚ) : ℝ)
      = ((467269/10000000 : ℚ) : ℝ) * ((971617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c459 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((89333/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1165237/10000000) (δ := 817/50000000) (ψ := 3441/250000) 323 315
    (log_br_459).1 (log_br_459).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t459 : ((1042310087/25000000000 : ℚ) : ℝ) ≤ stT323 459 := by
  have hc : ((89323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((459 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c459).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_459).1
  have hw2 : ((459 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11669/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1042310087/25000000000 : ℚ) : ℝ)
      = ((11669/250000 : ℚ) : ℝ) * ((89323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c460 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((78213/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2922519/10000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 315
    (log_br_460).1 (log_br_460).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t460 : ((9114410659/500000000000 : ℚ) : ℝ) ≤ stT323 460 := by
  have hc : ((78193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((460 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c460).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_460).1
  have hw2 : ((460 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9114410659/500000000000 : ℚ) : ℝ)
      = ((116563/2500000 : ℚ) : ℝ) * ((78193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c461 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-147587/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2338043/5000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 315
    (log_br_461).1 (log_br_461).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t461 : ((-68761489839/5000000000000 : ℚ) : ℝ) ≤ stT323 461 := by
  have hc : ((-147637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((461 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c461).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_461).2
  have h0 : (0:ℝ) ≤ ((461 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68761489839/5000000000000 : ℚ) : ℝ)
      = ((465747/10000000 : ℚ) : ℝ) * ((-147637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c462 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-841209/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6425777/10000000) (δ := 16163/1000000000) (ψ := 3441/250000) 323 315
    (log_br_462).1 (log_br_462).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t462 : ((-391413123087/10000000000000 : ℚ) : ℝ) ≤ stT323 462 := by
  have hc : ((-841309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((462 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c462).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_462).2
  have h0 : (0:ℝ) ≤ ((462 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-391413123087/10000000000000 : ℚ) : ℝ)
      = ((465243/10000000 : ℚ) : ℝ) * ((-841309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c463 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-991933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753621/1000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 316
    (log_br_463).1 (log_br_463).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t463 : ((-23051870821/500000000000 : ℚ) : ℝ) ≤ stT323 463 := by
  have hc : ((-992033/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((463 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c463).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_463).2
  have h0 : (0:ℝ) ≤ ((463 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23051870821/500000000000 : ℚ) : ℝ)
      = ((23237/500000 : ℚ) : ℝ) * ((-992033/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c464 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-135861/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5794029/10000000) (δ := 16333/1000000000) (ψ := 3441/250000) 323 316
    (log_br_464).1 (log_br_464).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t464 : ((-63081259559/2000000000000 : ℚ) : ℝ) ≤ stT323 464 := by
  have hc : ((-135881/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((464 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c464).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_464).2
  have h0 : (0:ℝ) ≤ ((464 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63081259559/2000000000000 : ℚ) : ℝ)
      = ((464239/10000000 : ℚ) : ℝ) * ((-135881/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c465 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-25703/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2027781/5000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 316
    (log_br_465).1 (log_br_465).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t465 : ((-11942670467/5000000000000 : ℚ) : ℝ) ≤ stT323 465 := by
  have hc : ((-25753/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((465 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c465).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_465).2
  have h0 : (0:ℝ) ≤ ((465 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11942670467/5000000000000 : ℚ) : ℝ)
      = ((463739/10000000 : ℚ) : ℝ) * ((-25753/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c466 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((599151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -232089/1000000) (δ := 1627/100000000) (ψ := 3441/250000) 323 316
    (log_br_466).1 (log_br_466).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t466 : ((277504984291/10000000000000 : ℚ) : ℝ) ≤ stT323 466 := by
  have hc : ((599051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((466 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c466).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_466).1
  have hw2 : ((466 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((463241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((277504984291/10000000000000 : ℚ) : ℝ)
      = ((463241/10000000 : ℚ) : ℝ) * ((599051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c467 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((972287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -589933/10000000) (δ := 1627/100000000) (ψ := 3441/250000) 323 316
    (log_br_467).1 (log_br_467).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t467 : ((56234212641/1250000000000 : ℚ) : ℝ) ≤ stT323 467 := by
  have hc : ((972187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((467 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c467).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_467).1
  have hw2 : ((467 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((57843/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56234212641/1250000000000 : ℚ) : ℝ)
      = ((57843/1250000 : ℚ) : ℝ) * ((972187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c468 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((179659/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1137309/10000000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 316
    (log_br_468).1 (log_br_468).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t468 : ((332152511/8000000000 : ℚ) : ℝ) ≤ stT323 468 := by
  have hc : ((179639/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((468 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c468).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_468).1
  have hw2 : ((468 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((332152511/8000000000 : ℚ) : ℝ)
      = ((1849/40000 : ℚ) : ℝ) * ((179639/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c469 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((206811/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1430459/5000000) (δ := 1617/100000000) (ψ := 3441/250000) 323 316
    (log_br_469).1 (log_br_469).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t469 : ((95473339077/5000000000000 : ℚ) : ℝ) ≤ stT323 469 := by
  have hc : ((206761/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((469 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c469).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_469).1
  have hw2 : ((469 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((461757/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95473339077/5000000000000 : ℚ) : ℝ)
      = ((461757/10000000 : ℚ) : ℝ) * ((206761/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c470 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-258557/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1145203/2500000) (δ := 16233/1000000000) (ψ := 3441/250000) 323 316
    (log_br_470).1 (log_br_470).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t470 : ((-59654839881/5000000000000 : ℚ) : ℝ) ≤ stT323 470 := by
  have hc : ((-258657/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((470 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c470).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_470).2
  have h0 : (0:ℝ) ≤ ((470 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59654839881/5000000000000 : ℚ) : ℝ)
      = ((230633/5000000 : ℚ) : ℝ) * ((-258657/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c471 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-81227/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6297073/10000000) (δ := 1627/100000000) (ψ := 3441/250000) 323 316
    (log_br_471).1 (log_br_471).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t471 : ((-4679007489/125000000000 : ℚ) : ℝ) ≤ stT323 471 := by
  have hc : ((-81237/100000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((471 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c471).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_471).2
  have h0 : (0:ℝ) ≤ ((471 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4679007489/125000000000 : ℚ) : ℝ)
      = ((57597/1250000 : ℚ) : ℝ) * ((-81237/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c472 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-998061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -962283/1250000) (δ := 8113/500000000) (ψ := 3441/250000) 323 317
    (log_br_472).1 (log_br_472).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t472 : ((-897346739/19531250000 : ℚ) : ℝ) ≤ stT323 472 := by
  have hc : ((-998161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((472 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c472).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_472).2
  have h0 : (0:ℝ) ≤ ((472 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-897346739/19531250000 : ℚ) : ℝ)
      = ((3596/78125 : ℚ) : ℝ) * ((-998161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c473 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-91811/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5989271/10000000) (δ := 8113/500000000) (ψ := 3441/250000) 323 317
    (log_br_473).1 (log_br_473).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t473 : ((-84441074247/2500000000000 : ℚ) : ℝ) ≤ stT323 473 := by
  have hc : ((-183647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((473 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c473).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_473).2
  have h0 : (0:ℝ) ≤ ((473 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84441074247/2500000000000 : ℚ) : ℝ)
      = ((459801/10000000 : ℚ) : ℝ) * ((-183647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c474 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-35563/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4283831/10000000) (δ := 8113/500000000) (ψ := 3441/250000) 323 317
    (log_br_474).1 (log_br_474).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t474 : ((-1021633613/156250000000 : ℚ) : ℝ) ≤ stT323 474 := by
  have hc : ((-8897/62500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((474 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c474).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_474).2
  have h0 : (0:ℝ) ≤ ((474 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1021633613/156250000000 : ℚ) : ℝ)
      = ((114829/2500000 : ℚ) : ℝ) * ((-8897/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c475 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((64051/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -103281/400000) (δ := 8163/500000000) (ψ := 3441/250000) 323 317
    (log_br_475).1 (log_br_475).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t475 : ((58765697987/2500000000000 : ℚ) : ℝ) ≤ stT323 475 := by
  have hc : ((128077/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((475 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c475).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_475).1
  have hw2 : ((475 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458831/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58765697987/2500000000000 : ℚ) : ℝ)
      = ((458831/10000000 : ℚ) : ℝ) * ((128077/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c476 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((938153/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -220963/2500000) (δ := 16177/1000000000) (ψ := 3441/250000) 323 317
    (log_br_476).1 (log_br_476).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t476 : ((429955654497/10000000000000 : ℚ) : ℝ) ≤ stT323 476 := by
  have hc : ((938053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((476 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c476).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_476).1
  have hw2 : ((476 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429955654497/10000000000000 : ℚ) : ℝ)
      = ((458349/10000000 : ℚ) : ℝ) * ((938053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c477 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((29621/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 810767/10000000) (δ := 8163/500000000) (ψ := 3441/250000) 323 317
    (log_br_477).1 (log_br_477).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t477 : ((27122154381/625000000000 : ℚ) : ℝ) ≤ stT323 477 := by
  have hc : ((236943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((477 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c477).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_477).1
  have hw2 : ((477 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((114467/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27122154381/625000000000 : ℚ) : ℝ)
      = ((114467/2500000 : ℚ) : ℝ) * ((236943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c478 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((269829/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 500383/2000000) (δ := 16277/1000000000) (ψ := 3441/250000) 323 317
    (log_br_478).1 (log_br_478).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t478 : ((123393947031/5000000000000 : ℚ) : ℝ) ≤ stT323 478 := by
  have hc : ((269779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((478 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c478).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_478).1
  have hw2 : ((478 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((457389/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123393947031/5000000000000 : ℚ) : ℝ)
      = ((457389/10000000 : ℚ) : ℝ) * ((269779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c479 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-52391/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1047357/2500000) (δ := 8113/500000000) (ψ := 3441/250000) 323 317
    (log_br_479).1 (log_br_479).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t479 : ((-1497557637/312500000000 : ℚ) : ℝ) ≤ stT323 479 := by
  have hc : ((-52441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((479 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c479).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_479).2
  have h0 : (0:ℝ) ≤ ((479 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1497557637/312500000000 : ℚ) : ℝ)
      = ((28557/625000 : ℚ) : ℝ) * ((-52441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c480 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-7023/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117471/200000) (δ := 8113/500000000) (ψ := 3441/250000) 323 317
    (log_br_480).1 (log_br_480).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t480 : ((-50093851/1562500000 : ℚ) : ℝ) ≤ stT323 480 := by
  have hc : ((-439/625 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((480 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c480).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_480).2
  have h0 : (0:ℝ) ≤ ((480 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50093851/1562500000 : ℚ) : ℝ)
      = ((114109/2500000 : ℚ) : ℝ) * ((-439/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c481 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-992811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3777019/5000000) (δ := 8163/500000000) (ψ := 3441/250000) 323 317
    (log_br_481).1 (log_br_481).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t481 : ((-452728692471/10000000000000 : ℚ) : ℝ) ≤ stT323 481 := by
  have hc : ((-992911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((481 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c481).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_481).2
  have h0 : (0:ℝ) ≤ ((481 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-452728692471/10000000000000 : ℚ) : ℝ)
      = ((455961/10000000 : ℚ) : ℝ) * ((-992911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c482 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-426037/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1619207/2500000) (δ := 3237/200000000) (ψ := 3441/250000) 323 318
    (log_br_482).1 (log_br_482).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t482 : ((-3032461179/78125000000 : ℚ) : ℝ) ≤ stT323 482 := by
  have hc : ((-426087/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((482 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c482).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_482).2
  have h0 : (0:ℝ) ≤ ((482 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3032461179/78125000000 : ℚ) : ℝ)
      = ((7117/156250 : ℚ) : ℝ) * ((-426087/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c483 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-42923/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1200821/2500000) (δ := 3257/200000000) (ψ := 3441/250000) 323 318
    (log_br_483).1 (log_br_483).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t483 : ((-4884084867/312500000000 : ℚ) : ℝ) ≤ stT323 483 := by
  have hc : ((-85871/250000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((483 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c483).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_483).2
  have h0 : (0:ℝ) ≤ ((483 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4884084867/312500000000 : ℚ) : ℝ)
      = ((56877/1250000 : ℚ) : ℝ) * ((-85871/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c484 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((156117/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -783283/2500000) (δ := 3237/200000000) (ψ := 3441/250000) 323 318
    (log_br_484).1 (log_br_484).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t484 : ((14187894903/1000000000000 : ℚ) : ℝ) ≤ stT323 484 := by
  have hc : ((156067/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((484 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c484).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_484).1
  have hw2 : ((484 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14187894903/1000000000000 : ℚ) : ℝ)
      = ((90909/2000000 : ℚ) : ℝ) * ((156067/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c485 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((41641/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1466533/10000000) (δ := 8109/500000000) (ψ := 3441/250000) 323 318
    (log_br_485).1 (log_br_485).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t485 : ((1181619271/31250000000 : ℚ) : ℝ) ≤ stT323 485 := by
  have hc : ((10409/12500 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((485 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c485).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_485).1
  have hw2 : ((485 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((113519/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1181619271/31250000000 : ℚ) : ℝ)
      = ((113519/2500000 : ℚ) : ℝ) * ((10409/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c486 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((199381/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49189/2500000) (δ := 3257/200000000) (ψ := 3441/250000) 323 318
    (log_br_486).1 (log_br_486).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t486 : ((90431943849/2000000000000 : ℚ) : ℝ) ≤ stT323 486 := by
  have hc : ((199361/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((486 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c486).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_486).1
  have hw2 : ((486 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453609/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90431943849/2000000000000 : ℚ) : ℝ)
      = ((453609/10000000 : ℚ) : ℝ) * ((199361/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c487 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((736693/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 464143/2500000) (δ := 3237/200000000) (ψ := 3441/250000) 323 318
    (log_br_487).1 (log_br_487).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t487 : ((333781961799/10000000000000 : ℚ) : ℝ) ≤ stT323 487 := by
  have hc : ((736593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((487 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c487).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_487).1
  have hw2 : ((487 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((453143/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333781961799/10000000000000 : ℚ) : ℝ)
      = ((453143/10000000 : ℚ) : ℝ) * ((736593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c488 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((82421/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3512997/10000000) (δ := 3257/200000000) (ψ := 3441/250000) 323 318
    (log_br_488).1 (log_br_488).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t488 : ((18643769769/2500000000000 : ℚ) : ℝ) ≤ stT323 488 := by
  have hc : ((82371/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((488 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c488).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_488).1
  have hw2 : ((488 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((226339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18643769769/2500000000000 : ℚ) : ℝ)
      = ((226339/5000000 : ℚ) : ℝ) * ((82371/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c489 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-95109/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5165949/10000000) (δ := 8109/500000000) (ψ := 3441/250000) 323 318
    (log_br_489).1 (log_br_489).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t489 : ((-5377356983/250000000000 : ℚ) : ℝ) ≤ stT323 489 := by
  have hc : ((-95129/200000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((489 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c489).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_489).2
  have h0 : (0:ℝ) ≤ ((489 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5377356983/250000000000 : ℚ) : ℝ)
      = ((56527/1250000 : ℚ) : ℝ) * ((-95129/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c490 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-914973/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6815591/10000000) (δ := 3237/200000000) (ψ := 3441/250000) 323 318
    (log_br_490).1 (log_br_490).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t490 : ((-206693944021/5000000000000 : ℚ) : ℝ) ≤ stT323 490 := by
  have hc : ((-915073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((490 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c490).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_490).2
  have h0 : (0:ℝ) ≤ ((490 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-206693944021/5000000000000 : ℚ) : ℝ)
      = ((225877/5000000 : ℚ) : ℝ) * ((-915073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c491 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-485289/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7246041/10000000) (δ := 4073/250000000) (ψ := 3441/250000) 323 319
    (log_br_491).1 (log_br_491).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t491 : ((-109515289333/2500000000000 : ℚ) : ℝ) ≤ stT323 491 := by
  have hc : ((-485339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((491 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c491).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_491).2
  have h0 : (0:ℝ) ≤ ((491 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109515289333/2500000000000 : ℚ) : ℝ)
      = ((225647/5000000 : ℚ) : ℝ) * ((-485339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c492 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-310667/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2801551/5000000) (δ := 16211/1000000000) (ψ := 3441/250000) 323 319
    (log_br_492).1 (log_br_492).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t492 : ((-28016419739/1000000000000 : ℚ) : ℝ) ≤ stT323 492 := by
  have hc : ((-310717/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((492 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c492).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_492).2
  have h0 : (0:ℝ) ≤ ((492 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28016419739/1000000000000 : ℚ) : ℝ)
      = ((90167/2000000 : ℚ) : ℝ) * ((-310717/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c493 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-117/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1981777/5000000) (δ := 16211/1000000000) (ψ := 3441/250000) 323 319
    (log_br_493).1 (log_br_493).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t493 : ((-132636321/200000000000 : ℚ) : ℝ) ≤ stT323 493 := by
  have hc : ((-589/40000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((493 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c493).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_493).2
  have h0 : (0:ℝ) ≤ ((493 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132636321/200000000000 : ℚ) : ℝ)
      = ((225189/5000000 : ℚ) : ℝ) * ((-589/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c494 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((597117/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581809/2500000) (δ := 16211/1000000000) (ψ := 3441/250000) 323 319
    (log_br_494).1 (log_br_494).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t494 : ((268610485657/10000000000000 : ℚ) : ℝ) ≤ stT323 494 := by
  have hc : ((597017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((494 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c494).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_494).1
  have hw2 : ((494 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449921/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268610485657/10000000000000 : ℚ) : ℝ)
      = ((449921/10000000 : ℚ) : ℝ) * ((597017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c495 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((480841/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -694309/10000000) (δ := 4073/250000000) (ψ := 3441/250000) 323 319
    (log_br_495).1 (log_br_495).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t495 : ((108049603803/2500000000000 : ℚ) : ℝ) ≤ stT323 495 := by
  have hc : ((480791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((495 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c495).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_495).1
  have hw2 : ((495 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((224733/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108049603803/2500000000000 : ℚ) : ℝ)
      = ((224733/5000000 : ℚ) : ℝ) * ((480791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c496 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((930817/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 935387/10000000) (δ := 16211/1000000000) (ψ := 3441/250000) 323 319
    (log_br_496).1 (log_br_496).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t496 : ((417904032321/10000000000000 : ℚ) : ℝ) ≤ stT323 496 := by
  have hc : ((930717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((496 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c496).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_496).1
  have hw2 : ((496 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((417904032321/10000000000000 : ℚ) : ℝ)
      = ((449013/10000000 : ℚ) : ℝ) * ((930717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c497 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((519347/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2561773/10000000) (δ := 253/15625000) (ψ := 3441/250000) 323 319
    (log_br_497).1 (log_br_497).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t497 : ((232913953567/10000000000000 : ℚ) : ℝ) ≤ stT323 497 := by
  have hc : ((519247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((497 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c497).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_497).1
  have hw2 : ((497 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((448561/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((232913953567/10000000000000 : ℚ) : ℝ)
      = ((448561/10000000 : ℚ) : ℝ) * ((519247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c498 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-1287/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 261553/625000) (δ := 253/15625000) (ψ := 3441/250000) 323 319
    (log_br_498).1 (log_br_498).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t498 : ((-2309115983/500000000000 : ℚ) : ℝ) ≤ stT323 498 := by
  have hc : ((-5153/50000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((498 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c498).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_498).2
  have h0 : (0:ℝ) ≤ ((498 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2309115983/500000000000 : ℚ) : ℝ)
      = ((448111/10000000 : ℚ) : ℝ) * ((-5153/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c499 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-682429/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5804693/10000000) (δ := 253/15625000) (ψ := 3441/250000) 323 319
    (log_br_499).1 (log_br_499).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t499 : ((-152771148599/5000000000000 : ℚ) : ℝ) ≤ stT323 499 := by
  have hc : ((-682529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((499 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c499).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_499).2
  have h0 : (0:ℝ) ≤ ((499 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152771148599/5000000000000 : ℚ) : ℝ)
      = ((223831/5000000 : ℚ) : ℝ) * ((-682529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_c500 :
    |Real.cos (((323 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((-985061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1855327/2500000) (δ := 253/15625000) (ψ := 3441/250000) 323 319
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st323_t500 : ((-220288895727/5000000000000 : ℚ) : ℝ) ≤ stT323 500 := by
  have hc : ((-985161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((323 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((3441/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st323_c500).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_500).2
  have h0 : (0:ℝ) ≤ ((500 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-220288895727/5000000000000 : ℚ) : ℝ)
      = ((223607/5000000 : ℚ) : ℝ) * ((-985161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st323_p1 : ((199961/200000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT323 (i+1) := by
  rw [Finset.sum_range_one]
  exact st323_t1

theorem st323_p2 : ((25858462683/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT323 (i+1))
      = (∑ i ∈ Finset.range 1, stT323 (i+1)) + stT323 2 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 1
    simpa using h
  have hprev := st323_p1
  have hstep := st323_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p3 : ((-52681265943/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT323 (i+1))
      = (∑ i ∈ Finset.range 2, stT323 (i+1)) + stT323 3 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 2
    simpa using h
  have hprev := st323_p2
  have hstep := st323_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p4 : ((-187727548359/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT323 (i+1))
      = (∑ i ∈ Finset.range 3, stT323 (i+1)) + stT323 4 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 3
    simpa using h
  have hprev := st323_p3
  have hstep := st323_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p5 : ((-1380614470539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT323 (i+1))
      = (∑ i ∈ Finset.range 4, stT323 (i+1)) + stT323 5 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 4
    simpa using h
  have hprev := st323_p4
  have hstep := st323_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p6 : ((1815136109133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT323 (i+1))
      = (∑ i ∈ Finset.range 5, stT323 (i+1)) + stT323 6 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 5
    simpa using h
  have hprev := st323_p5
  have hstep := st323_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p7 : ((5521530608413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT323 (i+1))
      = (∑ i ∈ Finset.range 6, stT323 (i+1)) + stT323 7 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 6
    simpa using h
  have hprev := st323_p6
  have hstep := st323_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p8 : ((4162542266879/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT323 (i+1))
      = (∑ i ∈ Finset.range 7, stT323 (i+1)) + stT323 8 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 7
    simpa using h
  have hprev := st323_p7
  have hstep := st323_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p9 : ((5749508774849/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT323 (i+1))
      = (∑ i ∈ Finset.range 8, stT323 (i+1)) + stT323 9 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 8
    simpa using h
  have hprev := st323_p8
  have hstep := st323_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p10 : ((2344796913669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT323 (i+1))
      = (∑ i ∈ Finset.range 9, stT323 (i+1)) + stT323 10 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 9
    simpa using h
  have hprev := st323_p9
  have hstep := st323_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p11 : ((1133305242489/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT323 (i+1))
      = (∑ i ∈ Finset.range 10, stT323 (i+1)) + stT323 11 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 10
    simpa using h
  have hprev := st323_p10
  have hstep := st323_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p12 : ((221905774097/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT323 (i+1))
      = (∑ i ∈ Finset.range 11, stT323 (i+1)) + stT323 12 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 11
    simpa using h
  have hprev := st323_p11
  have hstep := st323_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p13 : ((528296102419/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT323 (i+1))
      = (∑ i ∈ Finset.range 12, stT323 (i+1)) + stT323 13 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 12
    simpa using h
  have hprev := st323_p12
  have hstep := st323_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p14 : ((9190090274723/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT323 (i+1))
      = (∑ i ∈ Finset.range 13, stT323 (i+1)) + stT323 14 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 13
    simpa using h
  have hprev := st323_p13
  have hstep := st323_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p15 : ((9821337282951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT323 (i+1))
      = (∑ i ∈ Finset.range 14, stT323 (i+1)) + stT323 15 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 14
    simpa using h
  have hprev := st323_p14
  have hstep := st323_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p16 : ((7360806298739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT323 (i+1))
      = (∑ i ∈ Finset.range 15, stT323 (i+1)) + stT323 16 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 15
    simpa using h
  have hprev := st323_p15
  have hstep := st323_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p17 : ((5873325149211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT323 (i+1))
      = (∑ i ∈ Finset.range 16, stT323 (i+1)) + stT323 17 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 16
    simpa using h
  have hprev := st323_p16
  have hstep := st323_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p18 : ((3831487978817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT323 (i+1))
      = (∑ i ∈ Finset.range 17, stT323 (i+1)) + stT323 18 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 17
    simpa using h
  have hprev := st323_p17
  have hstep := st323_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p19 : ((2338915666491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT323 (i+1))
      = (∑ i ∈ Finset.range 18, stT323 (i+1)) + stT323 19 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 18
    simpa using h
  have hprev := st323_p18
  have hstep := st323_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p20 : ((4574750115523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT323 (i+1))
      = (∑ i ∈ Finset.range 19, stT323 (i+1)) + stT323 20 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 19
    simpa using h
  have hprev := st323_p19
  have hstep := st323_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p21 : ((598729239487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT323 (i+1))
      = (∑ i ∈ Finset.range 20, stT323 (i+1)) + stT323 21 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 20
    simpa using h
  have hprev := st323_p20
  have hstep := st323_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p22 : ((822599386181/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT323 (i+1))
      = (∑ i ∈ Finset.range 21, stT323 (i+1)) + stT323 22 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 21
    simpa using h
  have hprev := st323_p21
  have hstep := st323_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p23 : ((4949206399513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT323 (i+1))
      = (∑ i ∈ Finset.range 22, stT323 (i+1)) + stT323 23 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 22
    simpa using h
  have hprev := st323_p22
  have hstep := st323_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p24 : ((3531502593253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT323 (i+1))
      = (∑ i ∈ Finset.range 23, stT323 (i+1)) + stT323 24 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 23
    simpa using h
  have hprev := st323_p23
  have hstep := st323_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p25 : ((1565073610039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT323 (i+1))
      = (∑ i ∈ Finset.range 24, stT323 (i+1)) + stT323 25 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 24
    simpa using h
  have hprev := st323_p24
  have hstep := st323_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p26 : ((-389675390221/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT323 (i+1))
      = (∑ i ∈ Finset.range 25, stT323 (i+1)) + stT323 26 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 25
    simpa using h
  have hprev := st323_p25
  have hstep := st323_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p27 : ((-423142060019/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT323 (i+1))
      = (∑ i ∈ Finset.range 26, stT323 (i+1)) + stT323 27 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 26
    simpa using h
  have hprev := st323_p26
  have hstep := st323_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p28 : ((-133070307023/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT323 (i+1))
      = (∑ i ∈ Finset.range 27, stT323 (i+1)) + stT323 28 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 27
    simpa using h
  have hprev := st323_p27
  have hstep := st323_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p29 : ((-1163025193901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT323 (i+1))
      = (∑ i ∈ Finset.range 28, stT323 (i+1)) + stT323 29 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 28
    simpa using h
  have hprev := st323_p28
  have hstep := st323_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p30 : ((-152985106399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT323 (i+1))
      = (∑ i ∈ Finset.range 29, stT323 (i+1)) + stT323 30 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 29
    simpa using h
  have hprev := st323_p29
  have hstep := st323_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p31 : ((-1919583820799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT323 (i+1))
      = (∑ i ∈ Finset.range 30, stT323 (i+1)) + stT323 31 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 30
    simpa using h
  have hprev := st323_p30
  have hstep := st323_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p32 : ((-982496367497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT323 (i+1))
      = (∑ i ∈ Finset.range 31, stT323 (i+1)) + stT323 32 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 31
    simpa using h
  have hprev := st323_p31
  have hstep := st323_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p33 : ((-1059908720687/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT323 (i+1))
      = (∑ i ∈ Finset.range 32, stT323 (i+1)) + stT323 33 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 32
    simpa using h
  have hprev := st323_p32
  have hstep := st323_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p34 : ((-1355898154427/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT323 (i+1))
      = (∑ i ∈ Finset.range 33, stT323 (i+1)) + stT323 34 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 33
    simpa using h
  have hprev := st323_p33
  have hstep := st323_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p35 : ((-1167919001747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT323 (i+1))
      = (∑ i ∈ Finset.range 34, stT323 (i+1)) + stT323 35 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 34
    simpa using h
  have hprev := st323_p34
  have hstep := st323_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p36 : ((-814077476617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT323 (i+1))
      = (∑ i ∈ Finset.range 35, stT323 (i+1)) + stT323 36 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 35
    simpa using h
  have hprev := st323_p35
  have hstep := st323_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p37 : ((-1980825399567/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT323 (i+1))
      = (∑ i ∈ Finset.range 36, stT323 (i+1)) + stT323 37 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 36
    simpa using h
  have hprev := st323_p36
  have hstep := st323_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p38 : ((-359459817489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT323 (i+1))
      = (∑ i ∈ Finset.range 37, stT323 (i+1)) + stT323 38 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 37
    simpa using h
  have hprev := st323_p37
  have hstep := st323_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p39 : ((-1137154446429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT323 (i+1))
      = (∑ i ∈ Finset.range 38, stT323 (i+1)) + stT323 39 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 38
    simpa using h
  have hprev := st323_p38
  have hstep := st323_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p40 : ((-2203588430037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT323 (i+1))
      = (∑ i ∈ Finset.range 39, stT323 (i+1)) + stT323 40 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 39
    simpa using h
  have hprev := st323_p39
  have hstep := st323_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p41 : ((-465608935041/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT323 (i+1))
      = (∑ i ∈ Finset.range 40, stT323 (i+1)) + stT323 41 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 40
    simpa using h
  have hprev := st323_p40
  have hstep := st323_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p42 : ((4944749487/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT323 (i+1))
      = (∑ i ∈ Finset.range 41, stT323 (i+1)) + stT323 42 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 41
    simpa using h
  have hprev := st323_p41
  have hstep := st323_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p43 : ((-211768749921/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT323 (i+1))
      = (∑ i ∈ Finset.range 42, stT323 (i+1)) + stT323 43 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 42
    simpa using h
  have hprev := st323_p42
  have hstep := st323_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p44 : ((-581186547429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT323 (i+1))
      = (∑ i ∈ Finset.range 43, stT323 (i+1)) + stT323 44 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 43
    simpa using h
  have hprev := st323_p43
  have hstep := st323_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p45 : ((-724742113029/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT323 (i+1))
      = (∑ i ∈ Finset.range 44, stT323 (i+1)) + stT323 45 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 44
    simpa using h
  have hprev := st323_p44
  have hstep := st323_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p46 : ((-7178083641/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT323 (i+1))
      = (∑ i ∈ Finset.range 45, stT323 (i+1)) + stT323 46 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 45
    simpa using h
  have hprev := st323_p45
  have hstep := st323_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p47 : ((-1007904252721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT323 (i+1))
      = (∑ i ∈ Finset.range 46, stT323 (i+1)) + stT323 47 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 46
    simpa using h
  have hprev := st323_p46
  have hstep := st323_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p48 : ((217331950327/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT323 (i+1))
      = (∑ i ∈ Finset.range 47, stT323 (i+1)) + stT323 48 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 47
    simpa using h
  have hprev := st323_p47
  have hstep := st323_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p49 : ((1746330650011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT323 (i+1))
      = (∑ i ∈ Finset.range 48, stT323 (i+1)) + stT323 49 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 48
    simpa using h
  have hprev := st323_p48
  have hstep := st323_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p50 : ((2872505231449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT323 (i+1))
      = (∑ i ∈ Finset.range 49, stT323 (i+1)) + stT323 50 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 49
    simpa using h
  have hprev := st323_p49
  have hstep := st323_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p51 : ((3884934276769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT323 (i+1))
      = (∑ i ∈ Finset.range 50, stT323 (i+1)) + stT323 51 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 50
    simpa using h
  have hprev := st323_p50
  have hstep := st323_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p52 : ((4898188125769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT323 (i+1))
      = (∑ i ∈ Finset.range 51, stT323 (i+1)) + stT323 52 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 51
    simpa using h
  have hprev := st323_p51
  have hstep := st323_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p53 : ((6015412499729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT323 (i+1))
      = (∑ i ∈ Finset.range 52, stT323 (i+1)) + stT323 53 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 52
    simpa using h
  have hprev := st323_p52
  have hstep := st323_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p54 : ((7281487837373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT323 (i+1))
      = (∑ i ∈ Finset.range 53, stT323 (i+1)) + stT323 54 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 53
    simpa using h
  have hprev := st323_p53
  have hstep := st323_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p55 : ((8629517376047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT323 (i+1))
      = (∑ i ∈ Finset.range 54, stT323 (i+1)) + stT323 55 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 54
    simpa using h
  have hprev := st323_p54
  have hstep := st323_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p56 : ((9835812829001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT323 (i+1))
      = (∑ i ∈ Finset.range 55, stT323 (i+1)) + stT323 56 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 55
    simpa using h
  have hprev := st323_p55
  have hstep := st323_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p57 : ((2107860182781/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT323 (i+1))
      = (∑ i ∈ Finset.range 56, stT323 (i+1)) + stT323 57 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 56
    simpa using h
  have hprev := st323_p56
  have hstep := st323_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p58 : ((2080155561733/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT323 (i+1))
      = (∑ i ∈ Finset.range 57, stT323 (i+1)) + stT323 58 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 57
    simpa using h
  have hprev := st323_p57
  have hstep := st323_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p59 : ((376314302041/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT323 (i+1))
      = (∑ i ∈ Finset.range 58, stT323 (i+1)) + stT323 59 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 58
    simpa using h
  have hprev := st323_p58
  have hstep := st323_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p60 : ((1626283962129/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT323 (i+1))
      = (∑ i ∈ Finset.range 59, stT323 (i+1)) + stT323 60 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 59
    simpa using h
  have hprev := st323_p59
  have hstep := st323_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p61 : ((7545054341191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT323 (i+1))
      = (∑ i ∈ Finset.range 60, stT323 (i+1)) + stT323 61 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 60
    simpa using h
  have hprev := st323_p60
  have hstep := st323_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p62 : ((8214631888417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT323 (i+1))
      = (∑ i ∈ Finset.range 61, stT323 (i+1)) + stT323 62 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 61
    simpa using h
  have hprev := st323_p61
  have hstep := st323_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p63 : ((946812907139/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT323 (i+1))
      = (∑ i ∈ Finset.range 62, stT323 (i+1)) + stT323 63 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 62
    simpa using h
  have hprev := st323_p62
  have hstep := st323_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p64 : ((980695907139/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT323 (i+1))
      = (∑ i ∈ Finset.range 63, stT323 (i+1)) + stT323 64 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 63
    simpa using h
  have hprev := st323_p63
  have hstep := st323_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p65 : ((4381315974133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT323 (i+1))
      = (∑ i ∈ Finset.range 64, stT323 (i+1)) + stT323 65 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 64
    simpa using h
  have hprev := st323_p64
  have hstep := st323_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p66 : ((7888919864861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT323 (i+1))
      = (∑ i ∈ Finset.range 65, stT323 (i+1)) + stT323 66 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 65
    simpa using h
  have hprev := st323_p65
  have hstep := st323_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p67 : ((8615308574911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT323 (i+1))
      = (∑ i ∈ Finset.range 66, stT323 (i+1)) + stT323 67 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 66
    simpa using h
  have hprev := st323_p66
  have hstep := st323_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p68 : ((385602702667/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT323 (i+1))
      = (∑ i ∈ Finset.range 67, stT323 (i+1)) + stT323 68 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 67
    simpa using h
  have hprev := st323_p67
  have hstep := st323_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p69 : ((1799901246273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT323 (i+1))
      = (∑ i ∈ Finset.range 68, stT323 (i+1)) + stT323 69 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 68
    simpa using h
  have hprev := st323_p68
  have hstep := st323_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p70 : ((8030651213507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT323 (i+1))
      = (∑ i ∈ Finset.range 69, stT323 (i+1)) + stT323 70 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 69
    simpa using h
  have hprev := st323_p69
  have hstep := st323_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p71 : ((2211289797271/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT323 (i+1))
      = (∑ i ∈ Finset.range 70, stT323 (i+1)) + stT323 71 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 70
    simpa using h
  have hprev := st323_p70
  have hstep := st323_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p72 : ((2382312956569/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT323 (i+1))
      = (∑ i ∈ Finset.range 71, stT323 (i+1)) + stT323 72 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 71
    simpa using h
  have hprev := st323_p71
  have hstep := st323_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p73 : ((2108672971793/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT323 (i+1))
      = (∑ i ∈ Finset.range 72, stT323 (i+1)) + stT323 73 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 72
    simpa using h
  have hprev := st323_p72
  have hstep := st323_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p74 : ((8382865175081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT323 (i+1))
      = (∑ i ∈ Finset.range 73, stT323 (i+1)) + stT323 74 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 73
    simpa using h
  have hprev := st323_p73
  have hstep := st323_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p75 : ((9474308399681/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT323 (i+1))
      = (∑ i ∈ Finset.range 74, stT323 (i+1)) + stT323 75 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 74
    simpa using h
  have hprev := st323_p74
  have hstep := st323_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p76 : ((8678625580541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT323 (i+1))
      = (∑ i ∈ Finset.range 75, stT323 (i+1)) + stT323 76 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 75
    simpa using h
  have hprev := st323_p75
  have hstep := st323_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p77 : ((8326227496373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT323 (i+1))
      = (∑ i ∈ Finset.range 76, stT323 (i+1)) + stT323 77 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 76
    simpa using h
  have hprev := st323_p76
  have hstep := st323_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p78 : ((1178561686811/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT323 (i+1))
      = (∑ i ∈ Finset.range 77, stT323 (i+1)) + stT323 78 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 77
    simpa using h
  have hprev := st323_p77
  have hstep := st323_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p79 : ((1074957395787/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT323 (i+1))
      = (∑ i ∈ Finset.range 78, stT323 (i+1)) + stT323 79 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 78
    simpa using h
  have hprev := st323_p78
  have hstep := st323_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p80 : ((2123831617371/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT323 (i+1))
      = (∑ i ∈ Finset.range 79, stT323 (i+1)) + stT323 80 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 79
    simpa using h
  have hprev := st323_p79
  have hstep := st323_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p81 : ((9408114155983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT323 (i+1))
      = (∑ i ∈ Finset.range 80, stT323 (i+1)) + stT323 81 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 80
    simpa using h
  have hprev := st323_p80
  have hstep := st323_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p82 : ((8329132269339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT323 (i+1))
      = (∑ i ∈ Finset.range 81, stT323 (i+1)) + stT323 82 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 81
    simpa using h
  have hprev := st323_p81
  have hstep := st323_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p83 : ((8932478635689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT323 (i+1))
      = (∑ i ∈ Finset.range 82, stT323 (i+1)) + stT323 83 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 82
    simpa using h
  have hprev := st323_p82
  have hstep := st323_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p84 : ((4544800453567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT323 (i+1))
      = (∑ i ∈ Finset.range 83, stT323 (i+1)) + stT323 84 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 83
    simpa using h
  have hprev := st323_p83
  have hstep := st323_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p85 : ((4146181798843/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT323 (i+1))
      = (∑ i ∈ Finset.range 84, stT323 (i+1)) + stT323 85 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 84
    simpa using h
  have hprev := st323_p84
  have hstep := st323_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p86 : ((9364178580933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT323 (i+1))
      = (∑ i ∈ Finset.range 85, stT323 (i+1)) + stT323 86 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 85
    simpa using h
  have hprev := st323_p85
  have hstep := st323_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p87 : ((4207435382259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT323 (i+1))
      = (∑ i ∈ Finset.range 86, stT323 (i+1)) + stT323 87 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 86
    simpa using h
  have hprev := st323_p86
  have hstep := st323_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p88 : ((2240109043969/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT323 (i+1))
      = (∑ i ∈ Finset.range 87, stT323 (i+1)) + stT323 88 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 87
    simpa using h
  have hprev := st323_p87
  have hstep := st323_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p89 : ((2232337138633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT323 (i+1))
      = (∑ i ∈ Finset.range 88, stT323 (i+1)) + stT323 89 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 88
    simpa using h
  have hprev := st323_p88
  have hstep := st323_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p90 : ((8482028378587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT323 (i+1))
      = (∑ i ∈ Finset.range 89, stT323 (i+1)) + stT323 90 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 89
    simpa using h
  have hprev := st323_p89
  have hstep := st323_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p91 : ((9280215926719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT323 (i+1))
      = (∑ i ∈ Finset.range 90, stT323 (i+1)) + stT323 91 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 90
    simpa using h
  have hprev := st323_p90
  have hstep := st323_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p92 : ((4144685093057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT323 (i+1))
      = (∑ i ∈ Finset.range 91, stT323 (i+1)) + stT323 92 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 91
    simpa using h
  have hprev := st323_p91
  have hstep := st323_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p93 : ((9325629539797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT323 (i+1))
      = (∑ i ∈ Finset.range 92, stT323 (i+1)) + stT323 93 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 92
    simpa using h
  have hprev := st323_p92
  have hstep := st323_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p94 : ((8355464723799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT323 (i+1))
      = (∑ i ∈ Finset.range 93, stT323 (i+1)) + stT323 94 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 93
    simpa using h
  have hprev := st323_p93
  have hstep := st323_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p95 : ((9188533210349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT323 (i+1))
      = (∑ i ∈ Finset.range 94, stT323 (i+1)) + stT323 95 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 94
    simpa using h
  have hprev := st323_p94
  have hstep := st323_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p96 : ((4262716342393/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT323 (i+1))
      = (∑ i ∈ Finset.range 95, stT323 (i+1)) + stT323 96 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 95
    simpa using h
  have hprev := st323_p95
  have hstep := st323_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p97 : ((4506712108961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT323 (i+1))
      = (∑ i ∈ Finset.range 96, stT323 (i+1)) + stT323 97 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 96
    simpa using h
  have hprev := st323_p96
  have hstep := st323_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p98 : ((8685786143137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT323 (i+1))
      = (∑ i ∈ Finset.range 97, stT323 (i+1)) + stT323 98 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 97
    simpa using h
  have hprev := st323_p97
  have hstep := st323_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p99 : ((4439021342989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT323 (i+1))
      = (∑ i ∈ Finset.range 98, stT323 (i+1)) + stT323 99 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 98
    simpa using h
  have hprev := st323_p98
  have hstep := st323_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p100 : ((4395064342989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT323 (i+1))
      = (∑ i ∈ Finset.range 99, stT323 (i+1)) + stT323 100 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 99
    simpa using h
  have hprev := st323_p99
  have hstep := st323_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p101 : ((4402746028629/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT323 (i+1))
      = (∑ i ∈ Finset.range 100, stT323 (i+1)) + stT323 101 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 100
    simpa using h
  have hprev := st323_p100
  have hstep := st323_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p102 : ((8830302170637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT323 (i+1))
      = (∑ i ∈ Finset.range 101, stT323 (i+1)) + stT323 102 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 101
    simpa using h
  have hprev := st323_p101
  have hstep := st323_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p103 : ((8795933860237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT323 (i+1))
      = (∑ i ∈ Finset.range 102, stT323 (i+1)) + stT323 103 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 102
    simpa using h
  have hprev := st323_p102
  have hstep := st323_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p104 : ((8809552155277/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT323 (i+1))
      = (∑ i ∈ Finset.range 103, stT323 (i+1)) + stT323 104 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 103
    simpa using h
  have hprev := st323_p103
  have hstep := st323_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p105 : ((8845218372577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT323 (i+1))
      = (∑ i ∈ Finset.range 104, stT323 (i+1)) + stT323 105 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 104
    simpa using h
  have hprev := st323_p104
  have hstep := st323_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p106 : ((8732098519873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT323 (i+1))
      = (∑ i ∈ Finset.range 105, stT323 (i+1)) + stT323 106 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 105
    simpa using h
  have hprev := st323_p105
  have hstep := st323_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p107 : ((8947984202977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT323 (i+1))
      = (∑ i ∈ Finset.range 106, stT323 (i+1)) + stT323 107 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 106
    simpa using h
  have hprev := st323_p106
  have hstep := st323_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p108 : ((2151725456691/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT323 (i+1))
      = (∑ i ∈ Finset.range 107, stT323 (i+1)) + stT323 108 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 107
    simpa using h
  have hprev := st323_p107
  have hstep := st323_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p109 : ((4544212451307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT323 (i+1))
      = (∑ i ∈ Finset.range 108, stT323 (i+1)) + stT323 109 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 108
    simpa using h
  have hprev := st323_p108
  have hstep := st323_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p110 : ((4230296200113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT323 (i+1))
      = (∑ i ∈ Finset.range 109, stT323 (i+1)) + stT323 110 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 109
    simpa using h
  have hprev := st323_p109
  have hstep := st323_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p111 : ((4612694470587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT323 (i+1))
      = (∑ i ∈ Finset.range 110, stT323 (i+1)) + stT323 111 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 110
    simpa using h
  have hprev := st323_p110
  have hstep := st323_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p112 : ((4175476128891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT323 (i+1))
      = (∑ i ∈ Finset.range 111, stT323 (i+1)) + stT323 112 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 111
    simpa using h
  have hprev := st323_p111
  have hstep := st323_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p113 : ((4642491398931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT323 (i+1))
      = (∑ i ∈ Finset.range 112, stT323 (i+1)) + stT323 113 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 112
    simpa using h
  have hprev := st323_p112
  have hstep := st323_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p114 : ((4181491594113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT323 (i+1))
      = (∑ i ∈ Finset.range 113, stT323 (i+1)) + stT323 114 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 113
    simpa using h
  have hprev := st323_p113
  have hstep := st323_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p115 : ((4591089313593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT323 (i+1))
      = (∑ i ∈ Finset.range 114, stT323 (i+1)) + stT323 115 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 114
    simpa using h
  have hprev := st323_p114
  have hstep := st323_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p116 : ((8564406241989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT323 (i+1))
      = (∑ i ∈ Finset.range 115, stT323 (i+1)) + stT323 116 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 115
    simpa using h
  have hprev := st323_p115
  have hstep := st323_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p117 : ((8888968607989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT323 (i+1))
      = (∑ i ∈ Finset.range 116, stT323 (i+1)) + stT323 117 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 116
    simpa using h
  have hprev := st323_p116
  have hstep := st323_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p118 : ((8920002998677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT323 (i+1))
      = (∑ i ∈ Finset.range 117, stT323 (i+1)) + stT323 118 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 117
    simpa using h
  have hprev := st323_p117
  have hstep := st323_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p119 : ((8521444274253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT323 (i+1))
      = (∑ i ∈ Finset.range 118, stT323 (i+1)) + stT323 119 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 118
    simpa using h
  have hprev := st323_p118
  have hstep := st323_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p120 : ((9229746497343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT323 (i+1))
      = (∑ i ∈ Finset.range 119, stT323 (i+1)) + stT323 120 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 119
    simpa using h
  have hprev := st323_p119
  have hstep := st323_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p121 : ((8342755499553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT323 (i+1))
      = (∑ i ∈ Finset.range 120, stT323 (i+1)) + stT323 121 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 120
    simpa using h
  have hprev := st323_p120
  have hstep := st323_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p122 : ((9217187315147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT323 (i+1))
      = (∑ i ∈ Finset.range 121, stT323 (i+1)) + stT323 122 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 121
    simpa using h
  have hprev := st323_p121
  have hstep := st323_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p123 : ((8567637772197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT323 (i+1))
      = (∑ i ∈ Finset.range 122, stT323 (i+1)) + stT323 123 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 122
    simpa using h
  have hprev := st323_p122
  have hstep := st323_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p124 : ((8814010307271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT323 (i+1))
      = (∑ i ∈ Finset.range 123, stT323 (i+1)) + stT323 124 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 123
    simpa using h
  have hprev := st323_p123
  have hstep := st323_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p125 : ((9051781203243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT323 (i+1))
      = (∑ i ∈ Finset.range 124, stT323 (i+1)) + stT323 125 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 124
    simpa using h
  have hprev := st323_p124
  have hstep := st323_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p126 : ((8390074295799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT323 (i+1))
      = (∑ i ∈ Finset.range 125, stT323 (i+1)) + stT323 126 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 125
    simpa using h
  have hprev := st323_p125
  have hstep := st323_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p127 : ((9267963981991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT323 (i+1))
      = (∑ i ∈ Finset.range 126, stT323 (i+1)) + stT323 127 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 126
    simpa using h
  have hprev := st323_p126
  have hstep := st323_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p128 : ((8476942602799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT323 (i+1))
      = (∑ i ∈ Finset.range 127, stT323 (i+1)) + stT323 128 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 127
    simpa using h
  have hprev := st323_p127
  have hstep := st323_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p129 : ((8883527369199/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT323 (i+1))
      = (∑ i ∈ Finset.range 128, stT323 (i+1)) + stT323 129 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 128
    simpa using h
  have hprev := st323_p128
  have hstep := st323_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p130 : ((9029453156297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT323 (i+1))
      = (∑ i ∈ Finset.range 129, stT323 (i+1)) + stT323 130 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 129
    simpa using h
  have hprev := st323_p129
  have hstep := st323_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p131 : ((4191216769831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT323 (i+1))
      = (∑ i ∈ Finset.range 130, stT323 (i+1)) + stT323 131 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 130
    simpa using h
  have hprev := st323_p130
  have hstep := st323_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p132 : ((925156905133/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT323 (i+1))
      = (∑ i ∈ Finset.range 131, stT323 (i+1)) + stT323 132 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 131
    simpa using h
  have hprev := st323_p131
  have hstep := st323_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p133 : ((107028628821/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT323 (i+1))
      = (∑ i ∈ Finset.range 132, stT323 (i+1)) + stT323 133 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 132
    simpa using h
  have hprev := st323_p132
  have hstep := st323_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p134 : ((1091367474981/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT323 (i+1))
      = (∑ i ∈ Finset.range 133, stT323 (i+1)) + stT323 134 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 133
    simpa using h
  have hprev := st323_p133
  have hstep := st323_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p135 : ((91759416443/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT323 (i+1))
      = (∑ i ∈ Finset.range 134, stT323 (i+1)) + stT323 135 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 134
    simpa using h
  have hprev := st323_p134
  have hstep := st323_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p136 : ((4174653193699/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT323 (i+1))
      = (∑ i ∈ Finset.range 135, stT323 (i+1)) + stT323 136 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 135
    simpa using h
  have hprev := st323_p135
  have hstep := st323_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p137 : ((9096601348657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT323 (i+1))
      = (∑ i ∈ Finset.range 136, stT323 (i+1)) + stT323 137 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 136
    simpa using h
  have hprev := st323_p136
  have hstep := st323_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p138 : ((4433709990159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT323 (i+1))
      = (∑ i ∈ Finset.range 137, stT323 (i+1)) + stT323 138 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 137
    simpa using h
  have hprev := st323_p137
  have hstep := st323_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p139 : ((1686694413741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT323 (i+1))
      = (∑ i ∈ Finset.range 138, stT323 (i+1)) + stT323 139 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 138
    simpa using h
  have hprev := st323_p138
  have hstep := st323_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p140 : ((9260380884153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT323 (i+1))
      = (∑ i ∈ Finset.range 139, stT323 (i+1)) + stT323 140 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 139
    simpa using h
  have hprev := st323_p139
  have hstep := st323_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p141 : ((8582300305401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT323 (i+1))
      = (∑ i ∈ Finset.range 140, stT323 (i+1)) + stT323 141 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 140
    simpa using h
  have hprev := st323_p140
  have hstep := st323_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p142 : ((4323349947261/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT323 (i+1))
      = (∑ i ∈ Finset.range 141, stT323 (i+1)) + stT323 142 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 141
    simpa using h
  have hprev := st323_p141
  have hstep := st323_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p143 : ((1155665988929/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT323 (i+1))
      = (∑ i ∈ Finset.range 142, stT323 (i+1)) + stT323 143 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 142
    simpa using h
  have hprev := st323_p142
  have hstep := st323_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p144 : ((2104424728999/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT323 (i+1))
      = (∑ i ∈ Finset.range 143, stT323 (i+1)) + stT323 144 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 143
    simpa using h
  have hprev := st323_p143
  have hstep := st323_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p145 : ((884927008117/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT323 (i+1))
      = (∑ i ∈ Finset.range 144, stT323 (i+1)) + stT323 145 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 144
    simpa using h
  have hprev := st323_p144
  have hstep := st323_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p146 : ((915235558427/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT323 (i+1))
      = (∑ i ∈ Finset.range 145, stT323 (i+1)) + stT323 146 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 145
    simpa using h
  have hprev := st323_p145
  have hstep := st323_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p147 : ((4177488952927/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT323 (i+1))
      = (∑ i ∈ Finset.range 146, stT323 (i+1)) + stT323 147 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 146
    simpa using h
  have hprev := st323_p146
  have hstep := st323_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p148 : ((70213840561/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT323 (i+1))
      = (∑ i ∈ Finset.range 147, stT323 (i+1)) + stT323 148 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 147
    simpa using h
  have hprev := st323_p147
  have hstep := st323_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p149 : ((4529854025323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT323 (i+1))
      = (∑ i ∈ Finset.range 148, stT323 (i+1)) + stT323 149 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 148
    simpa using h
  have hprev := st323_p148
  have hstep := st323_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p150 : ((4171777632979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT323 (i+1))
      = (∑ i ∈ Finset.range 149, stT323 (i+1)) + stT323 150 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 149
    simpa using h
  have hprev := st323_p149
  have hstep := st323_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p151 : ((4529948924737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT323 (i+1))
      = (∑ i ∈ Finset.range 150, stT323 (i+1)) + stT323 151 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 150
    simpa using h
  have hprev := st323_p150
  have hstep := st323_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p152 : ((900547412489/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT323 (i+1))
      = (∑ i ∈ Finset.range 151, stT323 (i+1)) + stT323 152 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 151
    simpa using h
  have hprev := st323_p151
  have hstep := st323_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p153 : ((521546252509/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT323 (i+1))
      = (∑ i ∈ Finset.range 152, stT323 (i+1)) + stT323 153 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 152
    simpa using h
  have hprev := st323_p152
  have hstep := st323_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p154 : ((1134930023803/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT323 (i+1))
      = (∑ i ∈ Finset.range 153, stT323 (i+1)) + stT323 154 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 153
    simpa using h
  have hprev := st323_p153
  have hstep := st323_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p155 : ((140652411851/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT323 (i+1))
      = (∑ i ∈ Finset.range 154, stT323 (i+1)) + stT323 155 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 154
    simpa using h
  have hprev := st323_p154
  have hstep := st323_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p156 : ((8342305598173/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT323 (i+1))
      = (∑ i ∈ Finset.range 155, stT323 (i+1)) + stT323 156 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 155
    simpa using h
  have hprev := st323_p155
  have hstep := st323_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p157 : ((9052128075089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT323 (i+1))
      = (∑ i ∈ Finset.range 156, stT323 (i+1)) + stT323 157 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 156
    simpa using h
  have hprev := st323_p156
  have hstep := st323_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p158 : ((9047703977051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT323 (i+1))
      = (∑ i ∈ Finset.range 157, stT323 (i+1)) + stT323 158 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 157
    simpa using h
  have hprev := st323_p157
  have hstep := st323_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p159 : ((8341477689167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT323 (i+1))
      = (∑ i ∈ Finset.range 158, stT323 (i+1)) + stT323 159 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 158
    simpa using h
  have hprev := st323_p158
  have hstep := st323_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p160 : ((4486814260051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT323 (i+1))
      = (∑ i ∈ Finset.range 159, stT323 (i+1)) + stT323 160 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 159
    simpa using h
  have hprev := st323_p159
  have hstep := st323_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p161 : ((142686170263/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT323 (i+1))
      = (∑ i ∈ Finset.range 160, stT323 (i+1)) + stT323 161 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 160
    simpa using h
  have hprev := st323_p160
  have hstep := st323_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p162 : ((8366298965257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT323 (i+1))
      = (∑ i ∈ Finset.range 161, stT323 (i+1)) + stT323 162 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 161
    simpa using h
  have hprev := st323_p161
  have hstep := st323_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p163 : ((8836371670997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT323 (i+1))
      = (∑ i ∈ Finset.range 162, stT323 (i+1)) + stT323 163 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 162
    simpa using h
  have hprev := st323_p162
  have hstep := st323_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p164 : ((9225813187769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT323 (i+1))
      = (∑ i ∈ Finset.range 163, stT323 (i+1)) + stT323 164 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 163
    simpa using h
  have hprev := st323_p163
  have hstep := st323_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p165 : ((1056719727999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT323 (i+1))
      = (∑ i ∈ Finset.range 164, stT323 (i+1)) + stT323 165 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 164
    simpa using h
  have hprev := st323_p164
  have hstep := st323_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p166 : ((2161677566573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT323 (i+1))
      = (∑ i ∈ Finset.range 165, stT323 (i+1)) + stT323 166 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 165
    simpa using h
  have hprev := st323_p165
  have hstep := st323_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p167 : ((2319049950083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT323 (i+1))
      = (∑ i ∈ Finset.range 166, stT323 (i+1)) + stT323 167 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 166
    simpa using h
  have hprev := st323_p166
  have hstep := st323_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p168 : ((8636214876077/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT323 (i+1))
      = (∑ i ∈ Finset.range 167, stT323 (i+1)) + stT323 168 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 167
    simpa using h
  have hprev := st323_p167
  have hstep := st323_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p169 : ((4224183948323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT323 (i+1))
      = (∑ i ∈ Finset.range 168, stT323 (i+1)) + stT323 169 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 168
    simpa using h
  have hprev := st323_p168
  have hstep := st323_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p170 : ((4606136622107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT323 (i+1))
      = (∑ i ∈ Finset.range 169, stT323 (i+1)) + stT323 170 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 169
    simpa using h
  have hprev := st323_p169
  have hstep := st323_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p171 : ((4453039295747/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT323 (i+1))
      = (∑ i ∈ Finset.range 170, stT323 (i+1)) + stT323 171 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 170
    simpa using h
  have hprev := st323_p170
  have hstep := st323_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p172 : ((416749405467/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT323 (i+1))
      = (∑ i ∈ Finset.range 171, stT323 (i+1)) + stT323 172 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 171
    simpa using h
  have hprev := st323_p171
  have hstep := st323_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p173 : ((1797034183299/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT323 (i+1))
      = (∑ i ∈ Finset.range 172, stT323 (i+1)) + stT323 173 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 172
    simpa using h
  have hprev := st323_p172
  have hstep := st323_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p174 : ((9175456546887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT323 (i+1))
      = (∑ i ∈ Finset.range 173, stT323 (i+1)) + stT323 174 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 173
    simpa using h
  have hprev := st323_p173
  have hstep := st323_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p175 : ((8419715017279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT323 (i+1))
      = (∑ i ∈ Finset.range 174, stT323 (i+1)) + stT323 175 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 174
    simpa using h
  have hprev := st323_p174
  have hstep := st323_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p176 : ((8639554370979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT323 (i+1))
      = (∑ i ∈ Finset.range 175, stT323 (i+1)) + stT323 176 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 175
    simpa using h
  have hprev := st323_p175
  have hstep := st323_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p177 : ((9278179120189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT323 (i+1))
      = (∑ i ∈ Finset.range 176, stT323 (i+1)) + stT323 177 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 176
    simpa using h
  have hprev := st323_p176
  have hstep := st323_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p178 : ((8738216267389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT323 (i+1))
      = (∑ i ∈ Finset.range 177, stT323 (i+1)) + stT323 178 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 177
    simpa using h
  have hprev := st323_p177
  have hstep := st323_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p179 : ((8361697624697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT323 (i+1))
      = (∑ i ∈ Finset.range 178, stT323 (i+1)) + stT323 179 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 178
    simpa using h
  have hprev := st323_p178
  have hstep := st323_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p180 : ((4536934337371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT323 (i+1))
      = (∑ i ∈ Finset.range 179, stT323 (i+1)) + stT323 180 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 179
    simpa using h
  have hprev := st323_p179
  have hstep := st323_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p181 : ((1141694676603/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT323 (i+1))
      = (∑ i ∈ Finset.range 180, stT323 (i+1)) + stT323 181 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 180
    simpa using h
  have hprev := st323_p180
  have hstep := st323_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p182 : ((4199163552037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT323 (i+1))
      = (∑ i ∈ Finset.range 181, stT323 (i+1)) + stT323 182 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 181
    simpa using h
  have hprev := st323_p181
  have hstep := st323_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p183 : ((8635971131933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT323 (i+1))
      = (∑ i ∈ Finset.range 182, stT323 (i+1)) + stT323 183 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 182
    simpa using h
  have hprev := st323_p182
  have hstep := st323_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p184 : ((9276822492379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT323 (i+1))
      = (∑ i ∈ Finset.range 183, stT323 (i+1)) + stT323 184 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 183
    simpa using h
  have hprev := st323_p183
  have hstep := st323_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p185 : ((4402479649867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT323 (i+1))
      = (∑ i ∈ Finset.range 184, stT323 (i+1)) + stT323 185 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 184
    simpa using h
  have hprev := st323_p184
  have hstep := st323_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p186 : ((4165240042213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT323 (i+1))
      = (∑ i ∈ Finset.range 185, stT323 (i+1)) + stT323 186 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 185
    simpa using h
  have hprev := st323_p185
  have hstep := st323_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p187 : ((895667707329/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT323 (i+1))
      = (∑ i ∈ Finset.range 186, stT323 (i+1)) + stT323 187 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 186
    simpa using h
  have hprev := st323_p186
  have hstep := st323_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p188 : ((4617164266059/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT323 (i+1))
      = (∑ i ∈ Finset.range 187, stT323 (i+1)) + stT323 188 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 187
    simpa using h
  have hprev := st323_p187
  have hstep := st323_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p189 : ((4264550325807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT323 (i+1))
      = (∑ i ∈ Finset.range 188, stT323 (i+1)) + stT323 189 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 188
    simpa using h
  have hprev := st323_p188
  have hstep := st323_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p190 : ((4223167666773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT323 (i+1))
      = (∑ i ∈ Finset.range 189, stT323 (i+1)) + stT323 190 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 189
    simpa using h
  have hprev := st323_p189
  have hstep := st323_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p191 : ((1146224647447/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT323 (i+1))
      = (∑ i ∈ Finset.range 190, stT323 (i+1)) + stT323 191 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 190
    simpa using h
  have hprev := st323_p190
  have hstep := st323_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p192 : ((283710703947/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT323 (i+1))
      = (∑ i ∈ Finset.range 191, stT323 (i+1)) + stT323 192 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 191
    simpa using h
  have hprev := st323_p191
  have hstep := st323_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p193 : ((65456197111/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT323 (i+1))
      = (∑ i ∈ Finset.range 192, stT323 (i+1)) + stT323 193 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 192
    simpa using h
  have hprev := st323_p192
  have hstep := st323_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p194 : ((4306163101653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT323 (i+1))
      = (∑ i ∈ Finset.range 193, stT323 (i+1)) + stT323 194 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 193
    simpa using h
  have hprev := st323_p193
  have hstep := st323_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p195 : ((4632791290421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT323 (i+1))
      = (∑ i ∈ Finset.range 194, stT323 (i+1)) + stT323 195 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 194
    simpa using h
  have hprev := st323_p194
  have hstep := st323_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p196 : ((4460513364367/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT323 (i+1))
      = (∑ i ∈ Finset.range 195, stT323 (i+1)) + stT323 196 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 195
    simpa using h
  have hprev := st323_p195
  have hstep := st323_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p197 : ((1664707002237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT323 (i+1))
      = (∑ i ∈ Finset.range 196, stT323 (i+1)) + stT323 197 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 196
    simpa using h
  have hprev := st323_p196
  have hstep := st323_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p198 : ((8748377203399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT323 (i+1))
      = (∑ i ∈ Finset.range 197, stT323 (i+1)) + stT323 198 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 197
    simpa using h
  have hprev := st323_p197
  have hstep := st323_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p199 : ((9291720312279/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT323 (i+1))
      = (∑ i ∈ Finset.range 198, stT323 (i+1)) + stT323 199 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 198
    simpa using h
  have hprev := st323_p198
  have hstep := st323_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p200 : ((1101496266637/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT323 (i+1))
      = (∑ i ∈ Finset.range 199, stT323 (i+1)) + stT323 200 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 199
    simpa using h
  have hprev := st323_p199
  have hstep := st323_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p201 : ((415665724643/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT323 (i+1))
      = (∑ i ∈ Finset.range 200, stT323 (i+1)) + stT323 201 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 200
    simpa using h
  have hprev := st323_p200
  have hstep := st323_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p202 : ((2206666123209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT323 (i+1))
      = (∑ i ∈ Finset.range 201, stT323 (i+1)) + stT323 202 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 201
    simpa using h
  have hprev := st323_p201
  have hstep := st323_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p203 : ((580870394493/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT323 (i+1))
      = (∑ i ∈ Finset.range 202, stT323 (i+1)) + stT323 203 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 202
    simpa using h
  have hprev := st323_p202
  have hstep := st323_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p204 : ((8763902071363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT323 (i+1))
      = (∑ i ∈ Finset.range 203, stT323 (i+1)) + stT323 204 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 203
    simpa using h
  have hprev := st323_p203
  have hstep := st323_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p205 : ((8312008833191/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT323 (i+1))
      = (∑ i ∈ Finset.range 204, stT323 (i+1)) + stT323 205 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 204
    simpa using h
  have hprev := st323_p204
  have hstep := st323_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p206 : ((8843687178957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT323 (i+1))
      = (∑ i ∈ Finset.range 205, stT323 (i+1)) + stT323 206 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 205
    simpa using h
  have hprev := st323_p205
  have hstep := st323_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p207 : ((9296239882237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT323 (i+1))
      = (∑ i ∈ Finset.range 206, stT323 (i+1)) + stT323 207 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 206
    simpa using h
  have hprev := st323_p206
  have hstep := st323_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p208 : ((8776416588413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT323 (i+1))
      = (∑ i ∈ Finset.range 207, stT323 (i+1)) + stT323 208 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 207
    simpa using h
  have hprev := st323_p207
  have hstep := st323_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p209 : ((8307401999523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT323 (i+1))
      = (∑ i ∈ Finset.range 208, stT323 (i+1)) + stT323 209 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 208
    simpa using h
  have hprev := st323_p208
  have hstep := st323_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p210 : ((4400409933269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT323 (i+1))
      = (∑ i ∈ Finset.range 209, stT323 (i+1)) + stT323 210 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 209
    simpa using h
  have hprev := st323_p209
  have hstep := st323_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p211 : ((4649765439149/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT323 (i+1))
      = (∑ i ∈ Finset.range 210, stT323 (i+1)) + stT323 211 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 210
    simpa using h
  have hprev := st323_p210
  have hstep := st323_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p212 : ((8848229192983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT323 (i+1))
      = (∑ i ∈ Finset.range 211, stT323 (i+1)) + stT323 212 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 211
    simpa using h
  have hprev := st323_p211
  have hstep := st323_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p213 : ((8309417119053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT323 (i+1))
      = (∑ i ∈ Finset.range 212, stT323 (i+1)) + stT323 213 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 212
    simpa using h
  have hprev := st323_p212
  have hstep := st323_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p214 : ((67968091671/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT323 (i+1))
      = (∑ i ∈ Finset.range 213, stT323 (i+1)) + stT323 214 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 213
    simpa using h
  have hprev := st323_p213
  have hstep := st323_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p215 : ((4641840728037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT323 (i+1))
      = (∑ i ∈ Finset.range 214, stT323 (i+1)) + stT323 215 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 214
    simpa using h
  have hprev := st323_p214
  have hstep := st323_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p216 : ((897471498447/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT323 (i+1))
      = (∑ i ∈ Finset.range 215, stT323 (i+1)) + stT323 216 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 215
    simpa using h
  have hprev := st323_p215
  have hstep := st323_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p217 : ((166947669169/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT323 (i+1))
      = (∑ i ∈ Finset.range 216, stT323 (i+1)) + stT323 217 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 216
    simpa using h
  have hprev := st323_p216
  have hstep := st323_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p218 : ((427586762161/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT323 (i+1))
      = (∑ i ∈ Finset.range 217, stT323 (i+1)) + stT323 218 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 217
    simpa using h
  have hprev := st323_p217
  have hstep := st323_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p219 : ((2302994736321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT323 (i+1))
      = (∑ i ∈ Finset.range 218, stT323 (i+1)) + stT323 219 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 218
    simpa using h
  have hprev := st323_p218
  have hstep := st323_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p220 : ((2283669467521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT323 (i+1))
      = (∑ i ∈ Finset.range 219, stT323 (i+1)) + stT323 220 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 219
    simpa using h
  have hprev := st323_p219
  have hstep := st323_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p221 : ((8461963837031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT323 (i+1))
      = (∑ i ∈ Finset.range 220, stT323 (i+1)) + stT323 221 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 220
    simpa using h
  have hprev := st323_p220
  have hstep := st323_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p222 : ((839242324679/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT323 (i+1))
      = (∑ i ∈ Finset.range 221, stT323 (i+1)) + stT323 222 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 221
    simpa using h
  have hprev := st323_p221
  have hstep := st323_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p223 : ((2261363224477/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT323 (i+1))
      = (∑ i ∈ Finset.range 222, stT323 (i+1)) + stT323 223 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 222
    simpa using h
  have hprev := st323_p222
  have hstep := st323_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p224 : ((2318372711049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT323 (i+1))
      = (∑ i ∈ Finset.range 223, stT323 (i+1)) + stT323 224 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 223
    simpa using h
  have hprev := st323_p223
  have hstep := st323_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p225 : ((868222521523/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT323 (i+1))
      = (∑ i ∈ Finset.range 224, stT323 (i+1)) + stT323 225 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 224
    simpa using h
  have hprev := st323_p224
  have hstep := st323_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p226 : ((51851717157/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT323 (i+1))
      = (∑ i ∈ Finset.range 225, stT323 (i+1)) + stT323 226 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 225
    simpa using h
  have hprev := st323_p225
  have hstep := st323_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p227 : ((2193912502329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT323 (i+1))
      = (∑ i ∈ Finset.range 226, stT323 (i+1)) + stT323 227 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 226
    simpa using h
  have hprev := st323_p226
  have hstep := st323_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p228 : ((2325078919491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT323 (i+1))
      = (∑ i ∈ Finset.range 227, stT323 (i+1)) + stT323 228 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 227
    simpa using h
  have hprev := st323_p227
  have hstep := st323_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p229 : ((4492019226549/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT323 (i+1))
      = (∑ i ∈ Finset.range 228, stT323 (i+1)) + stT323 229 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 228
    simpa using h
  have hprev := st323_p228
  have hstep := st323_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p230 : ((130646413569/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT323 (i+1))
      = (∑ i ∈ Finset.range 229, stT323 (i+1)) + stT323 230 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 229
    simpa using h
  have hprev := st323_p229
  have hstep := st323_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p231 : ((8470075158783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT323 (i+1))
      = (∑ i ∈ Finset.range 230, stT323 (i+1)) + stT323 231 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 230
    simpa using h
  have hprev := st323_p230
  have hstep := st323_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p232 : ((9126511961643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT323 (i+1))
      = (∑ i ∈ Finset.range 231, stT323 (i+1)) + stT323 232 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 231
    simpa using h
  have hprev := st323_p231
  have hstep := st323_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p233 : ((185016646169/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT323 (i+1))
      = (∑ i ∈ Finset.range 232, stT323 (i+1)) + stT323 233 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 232
    simpa using h
  have hprev := st323_p232
  have hstep := st323_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p234 : ((4321659461807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT323 (i+1))
      = (∑ i ∈ Finset.range 233, stT323 (i+1)) + stT323 234 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 233
    simpa using h
  have hprev := st323_p233
  have hstep := st323_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p235 : ((829018975207/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT323 (i+1))
      = (∑ i ∈ Finset.range 234, stT323 (i+1)) + stT323 235 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 234
    simpa using h
  have hprev := st323_p234
  have hstep := st323_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p236 : ((4378461880227/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT323 (i+1))
      = (∑ i ∈ Finset.range 235, stT323 (i+1)) + stT323 236 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 235
    simpa using h
  have hprev := st323_p235
  have hstep := st323_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p237 : ((4647473086749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT323 (i+1))
      = (∑ i ∈ Finset.range 236, stT323 (i+1)) + stT323 237 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 236
    simpa using h
  have hprev := st323_p236
  have hstep := st323_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p238 : ((4526085220077/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT323 (i+1))
      = (∑ i ∈ Finset.range 237, stT323 (i+1)) + stT323 238 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 237
    simpa using h
  have hprev := st323_p237
  have hstep := st323_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p239 : ((2103572508317/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT323 (i+1))
      = (∑ i ∈ Finset.range 238, stT323 (i+1)) + stT323 239 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 238
    simpa using h
  have hprev := st323_p238
  have hstep := st323_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p240 : ((83788418651/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT323 (i+1))
      = (∑ i ∈ Finset.range 239, stT323 (i+1)) + stT323 240 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 239
    simpa using h
  have hprev := st323_p239
  have hstep := st323_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p241 : ((2249345267323/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT323 (i+1))
      = (∑ i ∈ Finset.range 240, stT323 (i+1)) + stT323 241 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 240
    simpa using h
  have hprev := st323_p240
  have hstep := st323_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p242 : ((2328611573351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT323 (i+1))
      = (∑ i ∈ Finset.range 241, stT323 (i+1)) + stT323 242 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 241
    simpa using h
  have hprev := st323_p241
  have hstep := st323_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p243 : ((8847091645371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT323 (i+1))
      = (∑ i ∈ Finset.range 242, stT323 (i+1)) + stT323 243 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 242
    simpa using h
  have hprev := st323_p242
  have hstep := st323_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p244 : ((4154327224173/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT323 (i+1))
      = (∑ i ∈ Finset.range 243, stT323 (i+1)) + stT323 244 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 243
    simpa using h
  have hprev := st323_p243
  have hstep := st323_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p245 : ((170215308529/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT323 (i+1))
      = (∑ i ∈ Finset.range 244, stT323 (i+1)) + stT323 245 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 244
    simpa using h
  have hprev := st323_p244
  have hstep := st323_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p246 : ((4573426024457/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT323 (i+1))
      = (∑ i ∈ Finset.range 245, stT323 (i+1)) + stT323 246 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 245
    simpa using h
  have hprev := st323_p245
  have hstep := st323_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p247 : ((926918337447/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT323 (i+1))
      = (∑ i ∈ Finset.range 246, stT323 (i+1)) + stT323 247 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 246
    simpa using h
  have hprev := st323_p246
  have hstep := st323_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p248 : ((2174982912003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT323 (i+1))
      = (∑ i ∈ Finset.range 247, stT323 (i+1)) + stT323 248 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 247
    simpa using h
  have hprev := st323_p247
  have hstep := st323_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p249 : ((8277103357037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT323 (i+1))
      = (∑ i ∈ Finset.range 248, stT323 (i+1)) + stT323 249 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 248
    simpa using h
  have hprev := st323_p248
  have hstep := st323_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p250 : ((8615288429727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT323 (i+1))
      = (∑ i ∈ Finset.range 249, stT323 (i+1)) + stT323 250 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 249
    simpa using h
  have hprev := st323_p249
  have hstep := st323_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p251 : ((1844265491049/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 251, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 251, stT323 (i+1))
      = (∑ i ∈ Finset.range 250, stT323 (i+1)) + stT323 251 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 250
    simpa using h
  have hprev := st323_p250
  have hstep := st323_t251
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p252 : ((1844706953001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 252, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 252, stT323 (i+1))
      = (∑ i ∈ Finset.range 251, stT323 (i+1)) + stT323 252 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 251
    simpa using h
  have hprev := st323_p251
  have hstep := st323_t252
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p253 : ((1724394093807/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 253, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 253, stT323 (i+1))
      = (∑ i ∈ Finset.range 252, stT323 (i+1)) + stT323 253 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 252
    simpa using h
  have hprev := st323_p252
  have hstep := st323_t253
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p254 : ((1654373768943/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 254, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 254, stT323 (i+1))
      = (∑ i ∈ Finset.range 253, stT323 (i+1)) + stT323 254 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 253
    simpa using h
  have hprev := st323_p253
  have hstep := st323_t254
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p255 : ((8664277711163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 255, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 255, stT323 (i+1))
      = (∑ i ∈ Finset.range 254, stT323 (i+1)) + stT323 255 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 254
    simpa using h
  have hprev := st323_p254
  have hstep := st323_t255
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p256 : ((9246752086163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 256, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 256, stT323 (i+1))
      = (∑ i ∈ Finset.range 255, stT323 (i+1)) + stT323 256 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 255
    simpa using h
  have hprev := st323_p255
  have hstep := st323_t256
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p257 : ((2302447144233/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 257, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 257, stT323 (i+1))
      = (∑ i ∈ Finset.range 256, stT323 (i+1)) + stT323 257 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 256
    simpa using h
  have hprev := st323_p256
  have hstep := st323_t257
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p258 : ((8607637839051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 258, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 258, stT323 (i+1))
      = (∑ i ∈ Finset.range 257, stT323 (i+1)) + stT323 258 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 257
    simpa using h
  have hprev := st323_p257
  have hstep := st323_t258
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p259 : ((8267827363041/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 259, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 259, stT323 (i+1))
      = (∑ i ∈ Finset.range 258, stT323 (i+1)) + stT323 259 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 258
    simpa using h
  have hprev := st323_p258
  have hstep := st323_t259
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p260 : ((4325518920649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 260, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 260, stT323 (i+1))
      = (∑ i ∈ Finset.range 259, stT323 (i+1)) + stT323 260 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 259
    simpa using h
  have hprev := st323_p259
  have hstep := st323_t260
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p261 : ((4617740338573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 261, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 261, stT323 (i+1))
      = (∑ i ∈ Finset.range 260, stT323 (i+1)) + stT323 261 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 260
    simpa using h
  have hprev := st323_p260
  have hstep := st323_t261
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p262 : ((2308896271421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 262, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 262, stT323 (i+1))
      = (∑ i ∈ Finset.range 261, stT323 (i+1)) + stT323 262 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 261
    simpa using h
  have hprev := st323_p261
  have hstep := st323_t262
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p263 : ((2163579486093/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 263, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 263, stT323 (i+1))
      = (∑ i ∈ Finset.range 262, stT323 (i+1)) + stT323 263 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 262
    simpa using h
  have hprev := st323_p262
  have hstep := st323_t263
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p264 : ((516537428783/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 264, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 264, stT323 (i+1))
      = (∑ i ∈ Finset.range 263, stT323 (i+1)) + stT323 264 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 263
    simpa using h
  have hprev := st323_p263
  have hstep := st323_t264
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p265 : ((8578042269983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 265, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 265, stT323 (i+1))
      = (∑ i ∈ Finset.range 264, stT323 (i+1)) + stT323 265 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 264
    simpa using h
  have hprev := st323_p264
  have hstep := st323_t265
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p266 : ((4590531318533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 266, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 266, stT323 (i+1))
      = (∑ i ∈ Finset.range 265, stT323 (i+1)) + stT323 266 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 265
    simpa using h
  have hprev := st323_p265
  have hstep := st323_t266
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p267 : ((4644508836533/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 267, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 267, stT323 (i+1))
      = (∑ i ∈ Finset.range 266, stT323 (i+1)) + stT323 267 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 266
    simpa using h
  have hprev := st323_p266
  have hstep := st323_t267
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p268 : ((4382632190453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 268, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 268, stT323 (i+1))
      = (∑ i ∈ Finset.range 267, stT323 (i+1)) + stT323 268 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 267
    simpa using h
  have hprev := st323_p267
  have hstep := st323_t268
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p269 : ((8284370072431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 269, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 269, stT323 (i+1))
      = (∑ i ∈ Finset.range 268, stT323 (i+1)) + stT323 269 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 268
    simpa using h
  have hprev := st323_p268
  have hstep := st323_t269
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p270 : ((8458307105071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 270, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 270, stT323 (i+1))
      = (∑ i ∈ Finset.range 269, stT323 (i+1)) + stT323 270 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 269
    simpa using h
  have hprev := st323_p269
  have hstep := st323_t270
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p271 : ((9063418324911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 271, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 271, stT323 (i+1))
      = (∑ i ∈ Finset.range 270, stT323 (i+1)) + stT323 271 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 270
    simpa using h
  have hprev := st323_p270
  have hstep := st323_t271
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p272 : ((1167100784031/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 272, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 272, stT323 (i+1))
      = (∑ i ∈ Finset.range 271, stT323 (i+1)) + stT323 272 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 271
    simpa using h
  have hprev := st323_p271
  have hstep := st323_t272
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p273 : ((2234707683221/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 273, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 273, stT323 (i+1))
      = (∑ i ∈ Finset.range 272, stT323 (i+1)) + stT323 273 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 272
    simpa using h
  have hprev := st323_p272
  have hstep := st323_t273
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p274 : ((2091697270169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 274, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 274, stT323 (i+1))
      = (∑ i ∈ Finset.range 273, stT323 (i+1)) + stT323 274 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 273
    simpa using h
  have hprev := st323_p273
  have hstep := st323_t274
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p275 : ((65052137333/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 275, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 275, stT323 (i+1))
      = (∑ i ∈ Finset.range 274, stT323 (i+1)) + stT323 275 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 274
    simpa using h
  have hprev := st323_p274
  have hstep := st323_t275
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p276 : ((277021028231/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 276, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 276, stT323 (i+1))
      = (∑ i ∈ Finset.range 275, stT323 (i+1)) + stT323 276 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 275
    simpa using h
  have hprev := st323_p275
  have hstep := st323_t276
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p277 : ((9322861632331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 277, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 277, stT323 (i+1))
      = (∑ i ∈ Finset.range 276, stT323 (i+1)) + stT323 277 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 276
    simpa using h
  have hprev := st323_p276
  have hstep := st323_t277
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p278 : ((228688922247/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 278, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 278, stT323 (i+1))
      = (∑ i ∈ Finset.range 277, stT323 (i+1)) + stT323 278 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 277
    simpa using h
  have hprev := st323_p277
  have hstep := st323_t278
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p279 : ((855273340813/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 279, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 279, stT323 (i+1))
      = (∑ i ∈ Finset.range 278, stT323 (i+1)) + stT323 279 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 278
    simpa using h
  have hprev := st323_p278
  have hstep := st323_t279
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p280 : ((1650148004513/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 280, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 280, stT323 (i+1))
      = (∑ i ∈ Finset.range 279, stT323 (i+1)) + stT323 280 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 279
    simpa using h
  have hprev := st323_p279
  have hstep := st323_t280
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p281 : ((8598191635929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 281, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 281, stT323 (i+1))
      = (∑ i ∈ Finset.range 280, stT323 (i+1)) + stT323 281 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 280
    simpa using h
  have hprev := st323_p280
  have hstep := st323_t281
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p282 : ((35866925793/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 282, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 282, stT323 (i+1))
      = (∑ i ∈ Finset.range 281, stT323 (i+1)) + stT323 282 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 281
    simpa using h
  have hprev := st323_p281
  have hstep := st323_t282
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p283 : ((4658396873253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 283, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 283, stT323 (i+1))
      = (∑ i ∈ Finset.range 282, stT323 (i+1)) + stT323 283 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 282
    simpa using h
  have hprev := st323_p282
  have hstep := st323_t283
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p284 : ((8848110392457/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 284, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 284, stT323 (i+1))
      = (∑ i ∈ Finset.range 283, stT323 (i+1)) + stT323 284 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 283
    simpa using h
  have hprev := st323_p283
  have hstep := st323_t284
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p285 : ((4160626045123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 285, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 285, stT323 (i+1))
      = (∑ i ∈ Finset.range 284, stT323 (i+1)) + stT323 285 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 284
    simpa using h
  have hprev := st323_p284
  have hstep := st323_t285
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p286 : ((4171082806531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 286, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 286, stT323 (i+1))
      = (∑ i ∈ Finset.range 285, stT323 (i+1)) + stT323 286 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 285
    simpa using h
  have hprev := st323_p285
  have hstep := st323_t286
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p287 : ((8883953258069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 287, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 287, stT323 (i+1))
      = (∑ i ∈ Finset.range 286, stT323 (i+1)) + stT323 287 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 286
    simpa using h
  have hprev := st323_p286
  have hstep := st323_t287
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p288 : ((2332157310131/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 288, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 288, stT323 (i+1))
      = (∑ i ∈ Finset.range 287, stT323 (i+1)) + stT323 288 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 287
    simpa using h
  have hprev := st323_p287
  have hstep := st323_t288
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p289 : ((2293722558127/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 289, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 289, stT323 (i+1))
      = (∑ i ∈ Finset.range 288, stT323 (i+1)) + stT323 289 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 288
    simpa using h
  have hprev := st323_p288
  have hstep := st323_t289
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p290 : ((8598259763243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 290, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 290, stT323 (i+1))
      = (∑ i ∈ Finset.range 289, stT323 (i+1)) + stT323 290 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 289
    simpa using h
  have hprev := st323_p289
  have hstep := st323_t290
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p291 : ((8243589211601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 291, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 291, stT323 (i+1))
      = (∑ i ∈ Finset.range 290, stT323 (i+1)) + stT323 291 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 290
    simpa using h
  have hprev := st323_p290
  have hstep := st323_t291
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p292 : ((8502500289341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 292, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 292, stT323 (i+1))
      = (∑ i ∈ Finset.range 291, stT323 (i+1)) + stT323 292 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 291
    simpa using h
  have hprev := st323_p291
  have hstep := st323_t292
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p293 : ((9086628589943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 293, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 293, stT323 (i+1))
      = (∑ i ∈ Finset.range 292, stT323 (i+1)) + stT323 293 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 292
    simpa using h
  have hprev := st323_p292
  have hstep := st323_t293
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p294 : ((4677531266851/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 294, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 294, stT323 (i+1))
      = (∑ i ∈ Finset.range 293, stT323 (i+1)) + stT323 294 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 293
    simpa using h
  have hprev := st323_p293
  have hstep := st323_t294
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p295 : ((2254371536241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 295, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 295, stT323 (i+1))
      = (∑ i ∈ Finset.range 294, stT323 (i+1)) + stT323 295 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 294
    simpa using h
  have hprev := st323_p294
  have hstep := st323_t295
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p296 : ((8441927593711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 296, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 296, stT323 (i+1))
      = (∑ i ∈ Finset.range 295, stT323 (i+1)) + stT323 296 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 295
    simpa using h
  have hprev := st323_p295
  have hstep := st323_t296
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p297 : ((2061983706143/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 297, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 297, stT323 (i+1))
      = (∑ i ∈ Finset.range 296, stT323 (i+1)) + stT323 297 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 296
    simpa using h
  have hprev := st323_p296
  have hstep := st323_t297
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p298 : ((2160145407437/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 298, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 298, stT323 (i+1))
      = (∑ i ∈ Finset.range 297, stT323 (i+1)) + stT323 298 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 297
    simpa using h
  have hprev := st323_p297
  have hstep := st323_t298
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p299 : ((229999011819/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 299, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 299, stT323 (i+1))
      = (∑ i ∈ Finset.range 298, stT323 (i+1)) + stT323 299 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 298
    simpa using h
  have hprev := st323_p298
  have hstep := st323_t299
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p300 : ((29171767773/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 300, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 300, stT323 (i+1))
      = (∑ i ∈ Finset.range 299, stT323 (i+1)) + stT323 300 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 299
    simpa using h
  have hprev := st323_p299
  have hstep := st323_t300
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p301 : ((1113272688221/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 301, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 301, stT323 (i+1))
      = (∑ i ∈ Finset.range 300, stT323 (i+1)) + stT323 301 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 300
    simpa using h
  have hprev := st323_p300
  have hstep := st323_t301
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p302 : ((418174592111/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 302, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 302, stT323 (i+1))
      = (∑ i ∈ Finset.range 301, stT323 (i+1)) + stT323 302 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 301
    simpa using h
  have hprev := st323_p301
  have hstep := st323_t302
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p303 : ((330791572693/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 303, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 303, stT323 (i+1))
      = (∑ i ∈ Finset.range 302, stT323 (i+1)) + stT323 303 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 302
    simpa using h
  have hprev := st323_p302
  have hstep := st323_t303
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p304 : ((4359592040079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 304, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 304, stT323 (i+1))
      = (∑ i ∈ Finset.range 303, stT323 (i+1)) + stT323 304 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 303
    simpa using h
  have hprev := st323_p303
  have hstep := st323_t304
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p305 : ((4624314974841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 305, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 305, stT323 (i+1))
      = (∑ i ∈ Finset.range 304, stT323 (i+1)) + stT323 305 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 304
    simpa using h
  have hprev := st323_p304
  have hstep := st323_t305
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p306 : ((9318731023129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 306, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 306, stT323 (i+1))
      = (∑ i ∈ Finset.range 305, stT323 (i+1)) + stT323 306 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 305
    simpa using h
  have hprev := st323_p305
  have hstep := st323_t306
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p307 : ((34612882947/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 307, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 307, stT323 (i+1))
      = (∑ i ∈ Finset.range 306, stT323 (i+1)) + stT323 307 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 306
    simpa using h
  have hprev := st323_p306
  have hstep := st323_t307
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p308 : ((2084587484207/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 308, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 308, stT323 (i+1))
      = (∑ i ∈ Finset.range 307, stT323 (i+1)) + stT323 308 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 307
    simpa using h
  have hprev := st323_p307
  have hstep := st323_t308
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p309 : ((8273914492601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 309, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 309, stT323 (i+1))
      = (∑ i ∈ Finset.range 308, stT323 (i+1)) + stT323 309 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 308
    simpa using h
  have hprev := st323_p308
  have hstep := st323_t309
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p310 : ((8729215884563/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 310, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 310, stT323 (i+1))
      = (∑ i ∈ Finset.range 309, stT323 (i+1)) + stT323 310 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 309
    simpa using h
  have hprev := st323_p309
  have hstep := st323_t310
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p311 : ((9251511535323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 311, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 311, stT323 (i+1))
      = (∑ i ∈ Finset.range 310, stT323 (i+1)) + stT323 311 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 310
    simpa using h
  have hprev := st323_p310
  have hstep := st323_t311
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p312 : ((9327207582751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 312, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 312, stT323 (i+1))
      = (∑ i ∈ Finset.range 311, stT323 (i+1)) + stT323 312 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 311
    simpa using h
  have hprev := st323_p311
  have hstep := st323_t312
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p313 : ((1776920332857/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 313, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 313, stT323 (i+1))
      = (∑ i ∈ Finset.range 312, stT323 (i+1)) + stT323 313 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 312
    simpa using h
  have hprev := st323_p312
  have hstep := st323_t313
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p314 : ((8356169272413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 314, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 314, stT323 (i+1))
      = (∑ i ∈ Finset.range 313, stT323 (i+1)) + stT323 314 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 313
    simpa using h
  have hprev := st323_p313
  have hstep := st323_t314
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p315 : ((8252552081239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 315, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 315, stT323 (i+1))
      = (∑ i ∈ Finset.range 314, stT323 (i+1)) + stT323 315 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 314
    simpa using h
  have hprev := st323_p314
  have hstep := st323_t315
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p316 : ((86709867533/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 316, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 316, stT323 (i+1))
      = (∑ i ∈ Finset.range 315, stT323 (i+1)) + stT323 316 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 315
    simpa using h
  have hprev := st323_p315
  have hstep := st323_t316
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p317 : ((1841869871759/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 317, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 317, stT323 (i+1))
      = (∑ i ∈ Finset.range 316, stT323 (i+1)) + stT323 317 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 316
    simpa using h
  have hprev := st323_p316
  have hstep := st323_t317
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p318 : ((74848557959/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 318, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 318, stT323 (i+1))
      = (∑ i ∈ Finset.range 317, stT323 (i+1)) + stT323 318 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 317
    simpa using h
  have hprev := st323_p317
  have hstep := st323_t318
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p319 : ((8974643758411/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 319, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 319, stT323 (i+1))
      = (∑ i ∈ Finset.range 318, stT323 (i+1)) + stT323 319 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 318
    simpa using h
  have hprev := st323_p318
  have hstep := st323_t319
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p320 : ((8425573906909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 320, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 320, stT323 (i+1))
      = (∑ i ∈ Finset.range 319, stT323 (i+1)) + stT323 320 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 319
    simpa using h
  have hprev := st323_p319
  have hstep := st323_t320
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p321 : ((8221857314661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 321, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 321, stT323 (i+1))
      = (∑ i ∈ Finset.range 320, stT323 (i+1)) + stT323 321 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 320
    simpa using h
  have hprev := st323_p320
  have hstep := st323_t321
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p322 : ((8550635173599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 322, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 322, stT323 (i+1))
      = (∑ i ∈ Finset.range 321, stT323 (i+1)) + stT323 322 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 321
    simpa using h
  have hprev := st323_p321
  have hstep := st323_t322
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p323 : ((364237097719/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 323, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 323, stT323 (i+1))
      = (∑ i ∈ Finset.range 322, stT323 (i+1)) + stT323 323 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 322
    simpa using h
  have hprev := st323_p322
  have hstep := st323_t323
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p324 : ((1875457878767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 324, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 324, stT323 (i+1))
      = (∑ i ∈ Finset.range 323, stT323 (i+1)) + stT323 324 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 323
    simpa using h
  have hprev := st323_p323
  have hstep := st323_t324
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p325 : ((9118663380791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 325, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 325, stT323 (i+1))
      = (∑ i ∈ Finset.range 324, stT323 (i+1)) + stT323 325 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 324
    simpa using h
  have hprev := st323_p324
  have hstep := st323_t325
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p326 : ((8567180423719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 326, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 326, stT323 (i+1))
      = (∑ i ∈ Finset.range 325, stT323 (i+1)) + stT323 326 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 325
    simpa using h
  have hprev := st323_p325
  have hstep := st323_t326
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p327 : ((8221529288629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 327, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 327, stT323 (i+1))
      = (∑ i ∈ Finset.range 326, stT323 (i+1)) + stT323 327 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 326
    simpa using h
  have hprev := st323_p326
  have hstep := st323_t327
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p328 : ((8390555589469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 328, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 328, stT323 (i+1))
      = (∑ i ∈ Finset.range 327, stT323 (i+1)) + stT323 328 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 327
    simpa using h
  have hprev := st323_p327
  have hstep := st323_t328
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p329 : ((446045107237/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 329, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 329, stT323 (i+1))
      = (∑ i ∈ Finset.range 328, stT323 (i+1)) + stT323 329 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 328
    simpa using h
  have hprev := st323_p328
  have hstep := st323_t329
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p330 : ((4670238830989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 330, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 330, stT323 (i+1))
      = (∑ i ∈ Finset.range 329, stT323 (i+1)) + stT323 330 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 329
    simpa using h
  have hprev := st323_p329
  have hstep := st323_t330
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p331 : ((1159979965541/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 331, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 331, stT323 (i+1))
      = (∑ i ∈ Finset.range 330, stT323 (i+1)) + stT323 331 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 330
    simpa using h
  have hprev := st323_p330
  have hstep := st323_t331
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p332 : ((4397254647521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 332, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 332, stT323 (i+1))
      = (∑ i ∈ Finset.range 331, stT323 (i+1)) + stT323 332 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 331
    simpa using h
  have hprev := st323_p331
  have hstep := st323_t332
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p333 : ((8309765944761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 333, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 333, stT323 (i+1))
      = (∑ i ∈ Finset.range 332, stT323 (i+1)) + stT323 333 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 332
    simpa using h
  have hprev := st323_p332
  have hstep := st323_t333
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p334 : ((8245920354729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 334, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 334, stT323 (i+1))
      = (∑ i ∈ Finset.range 333, stT323 (i+1)) + stT323 334 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 333
    simpa using h
  have hprev := st323_p333
  have hstep := st323_t334
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p335 : ((8655898109843/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 335, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 335, stT323 (i+1))
      = (∑ i ∈ Finset.range 334, stT323 (i+1)) + stT323 335 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 334
    simpa using h
  have hprev := st323_p334
  have hstep := st323_t335
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p336 : ((9185656248659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 336, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 336, stT323 (i+1))
      = (∑ i ∈ Finset.range 335, stT323 (i+1)) + stT323 336 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 335
    simpa using h
  have hprev := st323_p335
  have hstep := st323_t336
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p337 : ((9382674552311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 337, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 337, stT323 (i+1))
      = (∑ i ∈ Finset.range 336, stT323 (i+1)) + stT323 337 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 336
    simpa using h
  have hprev := st323_p336
  have hstep := st323_t337
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p338 : ((2270356908649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 338, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 338, stT323 (i+1))
      = (∑ i ∈ Finset.range 337, stT323 (i+1)) + stT323 338 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 337
    simpa using h
  have hprev := st323_p337
  have hstep := st323_t338
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p339 : ((4269243420281/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 339, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 339, stT323 (i+1))
      = (∑ i ∈ Finset.range 338, stT323 (i+1)) + stT323 339 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 338
    simpa using h
  have hprev := st323_p338
  have hstep := st323_t339
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p340 : ((1026325712281/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 340, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 340, stT323 (i+1))
      = (∑ i ∈ Finset.range 339, stT323 (i+1)) + stT323 340 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 339
    simpa using h
  have hprev := st323_p339
  have hstep := st323_t340
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p341 : ((4185155509099/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 341, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 341, stT323 (i+1))
      = (∑ i ∈ Finset.range 340, stT323 (i+1)) + stT323 341 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 340
    simpa using h
  have hprev := st323_p340
  have hstep := st323_t341
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p342 : ((4441302018223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 342, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 342, stT323 (i+1))
      = (∑ i ∈ Finset.range 341, stT323 (i+1)) + stT323 342 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 341
    simpa using h
  have hprev := st323_p341
  have hstep := st323_t342
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p343 : ((9322761282113/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 343, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 343, stT323 (i+1))
      = (∑ i ∈ Finset.range 342, stT323 (i+1)) + stT323 343 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 342
    simpa using h
  have hprev := st323_p342
  have hstep := st323_t343
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p344 : ((186593240587/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 344, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 344, stT323 (i+1))
      = (∑ i ∈ Finset.range 343, stT323 (i+1)) + stT323 344 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 343
    simpa using h
  have hprev := st323_p343
  have hstep := st323_t344
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p345 : ((2224935212981/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 345, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 345, stT323 (i+1))
      = (∑ i ∈ Finset.range 344, stT323 (i+1)) + stT323 345 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 344
    simpa using h
  have hprev := st323_p344
  have hstep := st323_t345
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p346 : ((419217102377/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 346, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 346, stT323 (i+1))
      = (∑ i ∈ Finset.range 345, stT323 (i+1)) + stT323 346 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 345
    simpa using h
  have hprev := st323_p345
  have hstep := st323_t346
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p347 : ((4100142965129/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 347, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 347, stT323 (i+1))
      = (∑ i ∈ Finset.range 346, stT323 (i+1)) + stT323 347 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 346
    simpa using h
  have hprev := st323_p346
  have hstep := st323_t347
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p348 : ((4246922602713/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 348, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 348, stT323 (i+1))
      = (∑ i ∈ Finset.range 347, stT323 (i+1)) + stT323 348 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 347
    simpa using h
  have hprev := st323_p347
  have hstep := st323_t348
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p349 : ((9027972238497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 349, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 349, stT323 (i+1))
      = (∑ i ∈ Finset.range 348, stT323 (i+1)) + stT323 349 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 348
    simpa using h
  have hprev := st323_p348
  have hstep := st323_t349
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p350 : ((1875343047531/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 350, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 350, stT323 (i+1))
      = (∑ i ∈ Finset.range 349, stT323 (i+1)) + stT323 350 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 349
    simpa using h
  have hprev := st323_p349
  have hstep := st323_t350
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p351 : ((1158133756321/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 351, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 351, stT323 (i+1))
      = (∑ i ∈ Finset.range 350, stT323 (i+1)) + stT323 351 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 350
    simpa using h
  have hprev := st323_p350
  have hstep := st323_t351
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p352 : ((175661430899/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 352, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 352, stT323 (i+1))
      = (∑ i ∈ Finset.range 351, stT323 (i+1)) + stT323 352 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 351
    simpa using h
  have hprev := st323_p351
  have hstep := st323_t352
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p353 : ((4154852983033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 353, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 353, stT323 (i+1))
      = (∑ i ∈ Finset.range 352, stT323 (i+1)) + stT323 353 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 352
    simpa using h
  have hprev := st323_p352
  have hstep := st323_t353
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p354 : ((4106722921813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 354, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 354, stT323 (i+1))
      = (∑ i ∈ Finset.range 353, stT323 (i+1)) + stT323 354 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 353
    simpa using h
  have hprev := st323_p353
  have hstep := st323_t354
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p355 : ((856697495277/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 355, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 355, stT323 (i+1))
      = (∑ i ∈ Finset.range 354, stT323 (i+1)) + stT323 355 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 354
    simpa using h
  have hprev := st323_p354
  have hstep := st323_t355
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p356 : ((2273933586861/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 356, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 356, stT323 (i+1))
      = (∑ i ∈ Finset.range 355, stT323 (i+1)) + stT323 356 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 355
    simpa using h
  have hprev := st323_p355
  have hstep := st323_t356
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p357 : ((2348398318293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 357, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 357, stT323 (i+1))
      = (∑ i ∈ Finset.range 356, stT323 (i+1)) + stT323 357 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 356
    simpa using h
  have hprev := st323_p356
  have hstep := st323_t357
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p358 : ((2308629528111/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 358, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 358, stT323 (i+1))
      = (∑ i ∈ Finset.range 357, stT323 (i+1)) + stT323 358 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 357
    simpa using h
  have hprev := st323_p357
  have hstep := st323_t358
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p359 : ((1092662869053/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 359, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 359, stT323 (i+1))
      = (∑ i ∈ Finset.range 358, stT323 (i+1)) + stT323 359 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 358
    simpa using h
  have hprev := st323_p358
  have hstep := st323_t359
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p360 : ((8287657261067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 360, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 360, stT323 (i+1))
      = (∑ i ∈ Finset.range 359, stT323 (i+1)) + stT323 360 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 359
    simpa using h
  have hprev := st323_p359
  have hstep := st323_t360
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p361 : ((8213880389451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 361, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 361, stT323 (i+1))
      = (∑ i ∈ Finset.range 360, stT323 (i+1)) + stT323 361 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 360
    simpa using h
  have hprev := st323_p360
  have hstep := st323_t361
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p362 : ((8573232263283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 362, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 362, stT323 (i+1))
      = (∑ i ∈ Finset.range 361, stT323 (i+1)) + stT323 362 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 361
    simpa using h
  have hprev := st323_p361
  have hstep := st323_t362
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p363 : ((4548318334503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 363, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 363, stT323 (i+1))
      = (∑ i ∈ Finset.range 362, stT323 (i+1)) + stT323 363 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 362
    simpa using h
  have hprev := st323_p362
  have hstep := st323_t363
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p364 : ((4698212463663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 364, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 364, stT323 (i+1))
      = (∑ i ∈ Finset.range 363, stT323 (i+1)) + stT323 364 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 363
    simpa using h
  have hprev := st323_p363
  have hstep := st323_t364
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p365 : ((4626581365839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 365, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 365, stT323 (i+1))
      = (∑ i ∈ Finset.range 364, stT323 (i+1)) + stT323 365 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 364
    simpa using h
  have hprev := st323_p364
  have hstep := st323_t365
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p366 : ((4386854473423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 366, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 366, stT323 (i+1))
      = (∑ i ∈ Finset.range 365, stT323 (i+1)) + stT323 366 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 365
    simpa using h
  have hprev := st323_p365
  have hstep := st323_t366
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p367 : ((830858649903/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 367, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 367, stT323 (i+1))
      = (∑ i ∈ Finset.range 366, stT323 (i+1)) + stT323 367 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 366
    simpa using h
  have hprev := st323_p366
  have hstep := st323_t367
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p368 : ((1638903174251/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 368, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 368, stT323 (i+1))
      = (∑ i ∈ Finset.range 367, stT323 (i+1)) + stT323 368 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 367
    simpa using h
  have hprev := st323_p367
  have hstep := st323_t368
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p369 : ((851199878309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 369, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 369, stT323 (i+1))
      = (∑ i ∈ Finset.range 368, stT323 (i+1)) + stT323 369 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 368
    simpa using h
  have hprev := st323_p368
  have hstep := st323_t369
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p370 : ((1806278579743/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 370, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 370, stT323 (i+1))
      = (∑ i ∈ Finset.range 369, stT323 (i+1)) + stT323 370 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 369
    simpa using h
  have hprev := st323_p369
  have hstep := st323_t370
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p371 : ((9381272564099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 371, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 371, stT323 (i+1))
      = (∑ i ∈ Finset.range 370, stT323 (i+1)) + stT323 371 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 370
    simpa using h
  have hprev := st323_p370
  have hstep := st323_t371
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p372 : ((9314101405919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 372, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 372, stT323 (i+1))
      = (∑ i ∈ Finset.range 371, stT323 (i+1)) + stT323 372 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 371
    simpa using h
  have hprev := st323_p371
  have hstep := st323_t372
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p373 : ((4439604170871/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 373, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 373, stT323 (i+1))
      = (∑ i ∈ Finset.range 372, stT323 (i+1)) + stT323 373 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 372
    simpa using h
  have hprev := st323_p372
  have hstep := st323_t373
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p374 : ((4191898076807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 374, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 374, stT323 (i+1))
      = (∑ i ∈ Finset.range 373, stT323 (i+1)) + stT323 374 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 373
    simpa using h
  have hprev := st323_p373
  have hstep := st323_t374
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p375 : ((4087208710267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 375, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 375, stT323 (i+1))
      = (∑ i ∈ Finset.range 374, stT323 (i+1)) + stT323 375 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 374
    simpa using h
  have hprev := st323_p374
  have hstep := st323_t375
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p376 : ((131177136791/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 376, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 376, stT323 (i+1))
      = (∑ i ∈ Finset.range 375, stT323 (i+1)) + stT323 376 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 375
    simpa using h
  have hprev := st323_p375
  have hstep := st323_t376
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p377 : ((1111454808671/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 377, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 377, stT323 (i+1))
      = (∑ i ∈ Finset.range 376, stT323 (i+1)) + stT323 377 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 376
    simpa using h
  have hprev := st323_p376
  have hstep := st323_t377
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p378 : ((291257878931/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 378, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 378, stT323 (i+1))
      = (∑ i ∈ Finset.range 377, stT323 (i+1)) + stT323 378 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 377
    simpa using h
  have hprev := st323_p377
  have hstep := st323_t378
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p379 : ((2346935385703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 379, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 379, stT323 (i+1))
      = (∑ i ∈ Finset.range 378, stT323 (i+1)) + stT323 379 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 378
    simpa using h
  have hprev := st323_p378
  have hstep := st323_t379
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p380 : ((4524863907451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 380, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 380, stT323 (i+1))
      = (∑ i ∈ Finset.range 379, stT323 (i+1)) + stT323 380 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 379
    simpa using h
  have hprev := st323_p379
  have hstep := st323_t380
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p381 : ((4268681316283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 381, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 381, stT323 (i+1))
      = (∑ i ∈ Finset.range 380, stT323 (i+1)) + stT323 381 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 380
    simpa using h
  have hprev := st323_p380
  have hstep := st323_t381
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p382 : ((8197332063531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 382, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 382, stT323 (i+1))
      = (∑ i ∈ Finset.range 381, stT323 (i+1)) + stT323 382 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 381
    simpa using h
  have hprev := st323_p381
  have hstep := st323_t382
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p383 : ((8257241955627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 383, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 383, stT323 (i+1))
      = (∑ i ∈ Finset.range 382, stT323 (i+1)) + stT323 383 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 382
    simpa using h
  have hprev := st323_p382
  have hstep := st323_t383
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p384 : ((8675195031207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 384, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 384, stT323 (i+1))
      = (∑ i ∈ Finset.range 383, stT323 (i+1)) + stT323 384 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 383
    simpa using h
  have hprev := st323_p383
  have hstep := st323_t384
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p385 : ((2292867605717/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 385, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 385, stT323 (i+1))
      = (∑ i ∈ Finset.range 384, stT323 (i+1)) + stT323 385 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 384
    simpa using h
  have hprev := st323_p384
  have hstep := st323_t385
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p386 : ((941713607867/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 386, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 386, stT323 (i+1))
      = (∑ i ∈ Finset.range 385, stT323 (i+1)) + stT323 386 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 385
    simpa using h
  have hprev := st323_p385
  have hstep := st323_t386
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p387 : ((2312863085267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 387, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 387, stT323 (i+1))
      = (∑ i ∈ Finset.range 386, stT323 (i+1)) + stT323 387 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 386
    simpa using h
  have hprev := st323_p386
  have hstep := st323_t387
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p388 : ((4392431945107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 388, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 388, stT323 (i+1))
      = (∑ i ∈ Finset.range 387, stT323 (i+1)) + stT323 388 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 387
    simpa using h
  have hprev := st323_p387
  have hstep := st323_t388
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p389 : ((8323121386577/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 389, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 389, stT323 (i+1))
      = (∑ i ∈ Finset.range 388, stT323 (i+1)) + stT323 389 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 388
    simpa using h
  have hprev := st323_p388
  have hstep := st323_t389
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p390 : ((8165968950707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 390, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 390, stT323 (i+1))
      = (∑ i ∈ Finset.range 389, stT323 (i+1)) + stT323 390 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 389
    simpa using h
  have hprev := st323_p389
  have hstep := st323_t390
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p391 : ((8413541631931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 391, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 391, stT323 (i+1))
      = (∑ i ∈ Finset.range 390, stT323 (i+1)) + stT323 391 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 390
    simpa using h
  have hprev := st323_p390
  have hstep := st323_t391
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p392 : ((1780958639347/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 392, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 392, stT323 (i+1))
      = (∑ i ∈ Finset.range 391, stT323 (i+1)) + stT323 392 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 391
    simpa using h
  have hprev := st323_p391
  have hstep := st323_t392
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p393 : ((9324215112111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 393, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 393, stT323 (i+1))
      = (∑ i ∈ Finset.range 392, stT323 (i+1)) + stT323 393 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 392
    simpa using h
  have hprev := st323_p392
  have hstep := st323_t393
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p394 : ((1880994291667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 394, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 394, stT323 (i+1))
      = (∑ i ∈ Finset.range 393, stT323 (i+1)) + stT323 394 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 393
    simpa using h
  have hprev := st323_p393
  have hstep := st323_t394
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p395 : ((9097364127/10000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 395, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 395, stT323 (i+1))
      = (∑ i ∈ Finset.range 394, stT323 (i+1)) + stT323 395 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 394
    simpa using h
  have hprev := st323_p394
  have hstep := st323_t395
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p396 : ((8597130080893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 396, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 396, stT323 (i+1))
      = (∑ i ∈ Finset.range 395, stT323 (i+1)) + stT323 396 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 395
    simpa using h
  have hprev := st323_p395
  have hstep := st323_t396
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p397 : ((8219151704117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 397, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 397, stT323 (i+1))
      = (∑ i ∈ Finset.range 396, stT323 (i+1)) + stT323 397 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 396
    simpa using h
  have hprev := st323_p396
  have hstep := st323_t397
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p398 : ((2049760463693/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 398, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 398, stT323 (i+1))
      = (∑ i ∈ Finset.range 397, stT323 (i+1)) + stT323 398 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 397
    simpa using h
  have hprev := st323_p397
  have hstep := st323_t398
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p399 : ((106845959999/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 399, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 399, stT323 (i+1))
      = (∑ i ∈ Finset.range 398, stT323 (i+1)) + stT323 399 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 398
    simpa using h
  have hprev := st323_p398
  have hstep := st323_t399
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p400 : ((113095122499/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 400, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 400, stT323 (i+1))
      = (∑ i ∈ Finset.range 399, stT323 (i+1)) + stT323 400 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 399
    simpa using h
  have hprev := st323_p399
  have hstep := st323_t400
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p401 : ((23475429371/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 401, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 401, stT323 (i+1))
      = (∑ i ∈ Finset.range 400, stT323 (i+1)) + stT323 401 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 400
    simpa using h
  have hprev := st323_p400
  have hstep := st323_t401
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p402 : ((936600307861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 402, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 402, stT323 (i+1))
      = (∑ i ∈ Finset.range 401, stT323 (i+1)) + stT323 402 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 401
    simpa using h
  have hprev := st323_p401
  have hstep := st323_t402
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p403 : ((899142722273/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 403, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 403, stT323 (i+1))
      = (∑ i ∈ Finset.range 402, stT323 (i+1)) + stT323 403 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 402
    simpa using h
  have hprev := st323_p402
  have hstep := st323_t403
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p404 : ((4247736211233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 404, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 404, stT323 (i+1))
      = (∑ i ∈ Finset.range 403, stT323 (i+1)) + stT323 404 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 403
    simpa using h
  have hprev := st323_p403
  have hstep := st323_t404
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p405 : ((4089235015573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 405, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 405, stT323 (i+1))
      = (∑ i ∈ Finset.range 404, stT323 (i+1)) + stT323 405 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 404
    simpa using h
  have hprev := st323_p404
  have hstep := st323_t405
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p406 : ((4115178131307/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 406, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 406, stT323 (i+1))
      = (∑ i ∈ Finset.range 405, stT323 (i+1)) + stT323 406 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 405
    simpa using h
  have hprev := st323_p405
  have hstep := st323_t406
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p407 : ((215460201609/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 407, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 407, stT323 (i+1))
      = (∑ i ∈ Finset.range 406, stT323 (i+1)) + stT323 407 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 406
    simpa using h
  have hprev := st323_p406
  have hstep := st323_t407
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p408 : ((2277448935237/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 408, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 408, stT323 (i+1))
      = (∑ i ∈ Finset.range 407, stT323 (i+1)) + stT323 408 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 407
    simpa using h
  have hprev := st323_p407
  have hstep := st323_t408
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p409 : ((2353113664767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 409, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 409, stT323 (i+1))
      = (∑ i ∈ Finset.range 408, stT323 (i+1)) + stT323 409 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 408
    simpa using h
  have hprev := st323_p408
  have hstep := st323_t409
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p410 : ((4674206604529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 410, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 410, stT323 (i+1))
      = (∑ i ∈ Finset.range 409, stT323 (i+1)) + stT323 410 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 409
    simpa using h
  have hprev := st323_p409
  have hstep := st323_t410
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p411 : ((4478440234841/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 411, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 411, stT323 (i+1))
      = (∑ i ∈ Finset.range 410, stT323 (i+1)) + stT323 411 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 410
    simpa using h
  have hprev := st323_p410
  have hstep := st323_t411
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p412 : ((8468382922917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 412, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 412, stT323 (i+1))
      = (∑ i ∈ Finset.range 411, stT323 (i+1)) + stT323 412 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 411
    simpa using h
  have hprev := st323_p411
  have hstep := st323_t412
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p413 : ((1633572545069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 413, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 413, stT323 (i+1))
      = (∑ i ∈ Finset.range 412, stT323 (i+1)) + stT323 413 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 412
    simpa using h
  have hprev := st323_p412
  have hstep := st323_t413
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p414 : ((4114370497191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 414, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 414, stT323 (i+1))
      = (∑ i ∈ Finset.range 413, stT323 (i+1)) + stT323 414 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 413
    simpa using h
  have hprev := st323_p413
  have hstep := st323_t414
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p415 : ((4307147418151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 415, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 415, stT323 (i+1))
      = (∑ i ∈ Finset.range 414, stT323 (i+1)) + stT323 415 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 414
    simpa using h
  have hprev := st323_p414
  have hstep := st323_t415
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p416 : ((4550782815241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 416, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 416, stT323 (i+1))
      = (∑ i ∈ Finset.range 415, stT323 (i+1)) + stT323 416 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 415
    simpa using h
  have hprev := st323_p415
  have hstep := st323_t416
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p417 : ((2352848429939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 417, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 417, stT323 (i+1))
      = (∑ i ∈ Finset.range 416, stT323 (i+1)) + stT323 417 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 416
    simpa using h
  have hprev := st323_p416
  have hstep := st323_t417
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p418 : ((1171014164033/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 418, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 418, stT323 (i+1))
      = (∑ i ∈ Finset.range 417, stT323 (i+1)) + stT323 418 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 417
    simpa using h
  have hprev := st323_p417
  have hstep := st323_t418
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p419 : ((281179210331/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 419, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 419, stT323 (i+1))
      = (∑ i ∈ Finset.range 418, stT323 (i+1)) + stT323 419 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 418
    simpa using h
  have hprev := st323_p418
  have hstep := st323_t419
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p420 : ((8510598120811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 420, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 420, stT323 (i+1))
      = (∑ i ∈ Finset.range 419, stT323 (i+1)) + stT323 420 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 419
    simpa using h
  have hprev := st323_p419
  have hstep := st323_t420
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p421 : ((8180775645013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 421, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 421, stT323 (i+1))
      = (∑ i ∈ Finset.range 420, stT323 (i+1)) + stT323 421 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 420
    simpa using h
  have hprev := st323_p420
  have hstep := st323_t421
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p422 : ((8191985491189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 422, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 422, stT323 (i+1))
      = (∑ i ∈ Finset.range 421, stT323 (i+1)) + stT323 422 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 421
    simpa using h
  have hprev := st323_p421
  have hstep := st323_t422
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p423 : ((1707300323489/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 423, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 423, stT323 (i+1))
      = (∑ i ∈ Finset.range 422, stT323 (i+1)) + stT323 423 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 422
    simpa using h
  have hprev := st323_p422
  have hstep := st323_t423
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p424 : ((360879722737/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 424, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 424, stT323 (i+1))
      = (∑ i ∈ Finset.range 423, stT323 (i+1)) + stT323 424 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 423
    simpa using h
  have hprev := st323_p423
  have hstep := st323_t424
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p425 : ((9380023003383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 425, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 425, stT323 (i+1))
      = (∑ i ∈ Finset.range 424, stT323 (i+1)) + stT323 425 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 424
    simpa using h
  have hprev := st323_p424
  have hstep := st323_t425
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p426 : ((9414480714503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 426, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 426, stT323 (i+1))
      = (∑ i ∈ Finset.range 425, stT323 (i+1)) + stT323 426 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 425
    simpa using h
  have hprev := st323_p425
  have hstep := st323_t426
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p427 : ((9107864487509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 427, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 427, stT323 (i+1))
      = (∑ i ∈ Finset.range 426, stT323 (i+1)) + stT323 427 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 426
    simpa using h
  have hprev := st323_p426
  have hstep := st323_t427
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p428 : ((8628476514593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 428, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 428, stT323 (i+1))
      = (∑ i ∈ Finset.range 427, stT323 (i+1)) + stT323 428 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 427
    simpa using h
  have hprev := st323_p427
  have hstep := st323_t428
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p429 : ((257399381179/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 429, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 429, stT323 (i+1))
      = (∑ i ∈ Finset.range 428, stT323 (i+1)) + stT323 429 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 428
    simpa using h
  have hprev := st323_p428
  have hstep := st323_t429
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p430 : ((4071846415719/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 430, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 430, stT323 (i+1))
      = (∑ i ∈ Finset.range 429, stT323 (i+1)) + stT323 430 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 429
    simpa using h
  have hprev := st323_p429
  have hstep := st323_t430
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p431 : ((4198960632687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 431, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 431, stT323 (i+1))
      = (∑ i ∈ Finset.range 430, stT323 (i+1)) + stT323 431 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 430
    simpa using h
  have hprev := st323_p430
  have hstep := st323_t431
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p432 : ((8862061109499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 432, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 432, stT323 (i+1))
      = (∑ i ∈ Finset.range 431, stT323 (i+1)) + stT323 432 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 431
    simpa using h
  have hprev := st323_p431
  have hstep := st323_t432
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p433 : ((1161014595623/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 433, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 433, stT323 (i+1))
      = (∑ i ∈ Finset.range 432, stT323 (i+1)) + stT323 433 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 432
    simpa using h
  have hprev := st323_p432
  have hstep := st323_t433
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p434 : ((2362600539061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 434, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 434, stT323 (i+1))
      = (∑ i ∈ Finset.range 433, stT323 (i+1)) + stT323 434 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 433
    simpa using h
  have hprev := st323_p433
  have hstep := st323_t434
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p435 : ((2316087496689/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 435, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 435, stT323 (i+1))
      = (∑ i ∈ Finset.range 434, stT323 (i+1)) + stT323 435 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 434
    simpa using h
  have hprev := st323_p434
  have hstep := st323_t435
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p436 : ((4414565331687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 436, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 436, stT323 (i+1))
      = (∑ i ∈ Finset.range 435, stT323 (i+1)) + stT323 436 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 435
    simpa using h
  have hprev := st323_p435
  have hstep := st323_t436
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p437 : ((8373408113919/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 437, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 437, stT323 (i+1))
      = (∑ i ∈ Finset.range 436, stT323 (i+1)) + stT323 437 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 436
    simpa using h
  have hprev := st323_p436
  have hstep := st323_t437
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p438 : ((1626919217799/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 438, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 438, stT323 (i+1))
      = (∑ i ∈ Finset.range 437, stT323 (i+1)) + stT323 438 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 437
    simpa using h
  have hprev := st323_p437
  have hstep := st323_t438
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p439 : ((4117802834721/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 439, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 439, stT323 (i+1))
      = (∑ i ∈ Finset.range 438, stT323 (i+1)) + stT323 439 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 438
    simpa using h
  have hprev := st323_p438
  have hstep := st323_t439
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p440 : ((8622859504783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 440, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 440, stT323 (i+1))
      = (∑ i ∈ Finset.range 439, stT323 (i+1)) + stT323 440 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 439
    simpa using h
  have hprev := st323_p439
  have hstep := st323_t440
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p441 : ((9096086174413/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 441, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 441, stT323 (i+1))
      = (∑ i ∈ Finset.range 440, stT323 (i+1)) + stT323 441 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 440
    simpa using h
  have hprev := st323_p440
  have hstep := st323_t441
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p442 : ((9412696603449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 442, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 442, stT323 (i+1))
      = (∑ i ∈ Finset.range 441, stT323 (i+1)) + stT323 442 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 441
    simpa using h
  have hprev := st323_p441
  have hstep := st323_t442
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p443 : ((9411951623129/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 443, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 443, stT323 (i+1))
      = (∑ i ∈ Finset.range 442, stT323 (i+1)) + stT323 443 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 442
    simpa using h
  have hprev := st323_p442
  have hstep := st323_t443
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p444 : ((4547751884833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 444, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 444, stT323 (i+1))
      = (∑ i ∈ Finset.range 443, stT323 (i+1)) + stT323 444 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 443
    simpa using h
  have hprev := st323_p443
  have hstep := st323_t444
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p445 : ((862450778163/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 445, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 445, stT323 (i+1))
      = (∑ i ∈ Finset.range 444, stT323 (i+1)) + stT323 445 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 444
    simpa using h
  have hprev := st323_p444
  have hstep := st323_t445
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p446 : ((4118262781239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 446, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 446, stT323 (i+1))
      = (∑ i ∈ Finset.range 445, stT323 (i+1)) + stT323 446 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 445
    simpa using h
  have hprev := st323_p445
  have hstep := st323_t446
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p447 : ((812554601567/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 447, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 447, stT323 (i+1))
      = (∑ i ∈ Finset.range 446, stT323 (i+1)) + stT323 447 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 446
    simpa using h
  have hprev := st323_p446
  have hstep := st323_t447
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p448 : ((20864471183/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 448, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 448, stT323 (i+1))
      = (∑ i ∈ Finset.range 447, stT323 (i+1)) + stT323 448 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 447
    simpa using h
  have hprev := st323_p447
  have hstep := st323_t448
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p449 : ((439324260599/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 449, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 449, stT323 (i+1))
      = (∑ i ∈ Finset.range 448, stT323 (i+1)) + stT323 449 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 448
    simpa using h
  have hprev := st323_p448
  have hstep := st323_t449
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p450 : ((1153596735841/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 450, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 450, stT323 (i+1))
      = (∑ i ∈ Finset.range 449, stT323 (i+1)) + stT323 450 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 449
    simpa using h
  have hprev := st323_p449
  have hstep := st323_t450
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p451 : ((9454806655229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 451, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 451, stT323 (i+1))
      = (∑ i ∈ Finset.range 450, stT323 (i+1)) + stT323 451 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 450
    simpa using h
  have hprev := st323_p450
  have hstep := st323_t451
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p452 : ((584662412249/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 452, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 452, stT323 (i+1))
      = (∑ i ∈ Finset.range 451, stT323 (i+1)) + stT323 452 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 451
    simpa using h
  have hprev := st323_p451
  have hstep := st323_t452
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p453 : ((8978362608891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 453, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 453, stT323 (i+1))
      = (∑ i ∈ Finset.range 452, stT323 (i+1)) + stT323 453 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 452
    simpa using h
  have hprev := st323_p452
  have hstep := st323_t453
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p454 : ((8510135888403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 454, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 454, stT323 (i+1))
      = (∑ i ∈ Finset.range 453, stT323 (i+1)) + stT323 454 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 453
    simpa using h
  have hprev := st323_p453
  have hstep := st323_t454
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p455 : ((8176982640091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 455, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 455, stT323 (i+1))
      = (∑ i ∈ Finset.range 454, stT323 (i+1)) + stT323 455 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 454
    simpa using h
  have hprev := st323_p454
  have hstep := st323_t455
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p456 : ((8138975980211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 456, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 456, stT323 (i+1))
      = (∑ i ∈ Finset.range 455, stT323 (i+1)) + stT323 456 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 455
    simpa using h
  have hprev := st323_p455
  have hstep := st323_t456
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p457 : ((8413150258251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 457, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 457, stT323 (i+1))
      = (∑ i ∈ Finset.range 456, stT323 (i+1)) + stT323 457 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 456
    simpa using h
  have hprev := st323_p456
  have hstep := st323_t457
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p458 : ((554197297639/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 458, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 458, stT323 (i+1))
      = (∑ i ∈ Finset.range 457, stT323 (i+1)) + stT323 458 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 457
    simpa using h
  have hprev := st323_p457
  have hstep := st323_t458
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p459 : ((290127524907/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 459, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 459, stT323 (i+1))
      = (∑ i ∈ Finset.range 458, stT323 (i+1)) + stT323 459 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 458
    simpa using h
  have hprev := st323_p458
  have hstep := st323_t459
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p460 : ((2366592252551/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 460, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 460, stT323 (i+1))
      = (∑ i ∈ Finset.range 459, stT323 (i+1)) + stT323 460 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 459
    simpa using h
  have hprev := st323_p459
  have hstep := st323_t460
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p461 : ((4664423015263/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 461, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 461, stT323 (i+1))
      = (∑ i ∈ Finset.range 460, stT323 (i+1)) + stT323 461 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 460
    simpa using h
  have hprev := st323_p460
  have hstep := st323_t461
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p462 : ((8937432907439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 462, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 462, stT323 (i+1))
      = (∑ i ∈ Finset.range 461, stT323 (i+1)) + stT323 462 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 461
    simpa using h
  have hprev := st323_p461
  have hstep := st323_t462
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p463 : ((8476395491019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 463, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 463, stT323 (i+1))
      = (∑ i ∈ Finset.range 462, stT323 (i+1)) + stT323 463 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 462
    simpa using h
  have hprev := st323_p462
  have hstep := st323_t463
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p464 : ((1020123649153/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 464, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 464, stT323 (i+1))
      = (∑ i ∈ Finset.range 463, stT323 (i+1)) + stT323 464 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 463
    simpa using h
  have hprev := st323_p463
  have hstep := st323_t464
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p465 : ((813710385229/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 465, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 465, stT323 (i+1))
      = (∑ i ∈ Finset.range 464, stT323 (i+1)) + stT323 465 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 464
    simpa using h
  have hprev := st323_p464
  have hstep := st323_t465
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p466 : ((8414608836581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 466, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 466, stT323 (i+1))
      = (∑ i ∈ Finset.range 465, stT323 (i+1)) + stT323 466 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 465
    simpa using h
  have hprev := st323_p465
  have hstep := st323_t466
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p467 : ((8864482537709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 467, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 467, stT323 (i+1))
      = (∑ i ∈ Finset.range 466, stT323 (i+1)) + stT323 467 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 466
    simpa using h
  have hprev := st323_p466
  have hstep := st323_t467
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p468 : ((9279673176459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 468, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 468, stT323 (i+1))
      = (∑ i ∈ Finset.range 467, stT323 (i+1)) + stT323 468 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 467
    simpa using h
  have hprev := st323_p467
  have hstep := st323_t468
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p469 : ((9470619854613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 469, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 469, stT323 (i+1))
      = (∑ i ∈ Finset.range 468, stT323 (i+1)) + stT323 469 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 468
    simpa using h
  have hprev := st323_p468
  have hstep := st323_t469
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p470 : ((9351310174851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 470, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 470, stT323 (i+1))
      = (∑ i ∈ Finset.range 469, stT323 (i+1)) + stT323 470 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 469
    simpa using h
  have hprev := st323_p469
  have hstep := st323_t470
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p471 : ((8976989575731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 471, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 471, stT323 (i+1))
      = (∑ i ∈ Finset.range 470, stT323 (i+1)) + stT323 471 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 470
    simpa using h
  have hprev := st323_p470
  have hstep := st323_t471
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p472 : ((8517548045363/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 472, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 472, stT323 (i+1))
      = (∑ i ∈ Finset.range 471, stT323 (i+1)) + stT323 472 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 471
    simpa using h
  have hprev := st323_p471
  have hstep := st323_t472
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p473 : ((65438269987/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 473, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 473, stT323 (i+1))
      = (∑ i ∈ Finset.range 472, stT323 (i+1)) + stT323 473 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 472
    simpa using h
  have hprev := st323_p472
  have hstep := st323_t473
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p474 : ((8114399197143/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 474, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 474, stT323 (i+1))
      = (∑ i ∈ Finset.range 473, stT323 (i+1)) + stT323 474 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 473
    simpa using h
  have hprev := st323_p473
  have hstep := st323_t474
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p475 : ((8349461989091/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 475, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 475, stT323 (i+1))
      = (∑ i ∈ Finset.range 474, stT323 (i+1)) + stT323 475 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 474
    simpa using h
  have hprev := st323_p474
  have hstep := st323_t475
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p476 : ((2194854410897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 476, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 476, stT323 (i+1))
      = (∑ i ∈ Finset.range 475, stT323 (i+1)) + stT323 476 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 475
    simpa using h
  have hprev := st323_p475
  have hstep := st323_t476
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p477 : ((2303343028421/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 477, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 477, stT323 (i+1))
      = (∑ i ∈ Finset.range 476, stT323 (i+1)) + stT323 477 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 476
    simpa using h
  have hprev := st323_p476
  have hstep := st323_t477
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p478 : ((4730080003873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 478, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 478, stT323 (i+1))
      = (∑ i ∈ Finset.range 477, stT323 (i+1)) + stT323 478 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 477
    simpa using h
  have hprev := st323_p477
  have hstep := st323_t478
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p479 : ((4706119081681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 479, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 479, stT323 (i+1))
      = (∑ i ∈ Finset.range 478, stT323 (i+1)) + stT323 479 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 478
    simpa using h
  have hprev := st323_p478
  have hstep := st323_t479
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p480 : ((4545818758481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 480, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 480, stT323 (i+1))
      = (∑ i ∈ Finset.range 479, stT323 (i+1)) + stT323 480 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 479
    simpa using h
  have hprev := st323_p479
  have hstep := st323_t480
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p481 : ((8638908824491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 481, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 481, stT323 (i+1))
      = (∑ i ∈ Finset.range 480, stT323 (i+1)) + stT323 481 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 480
    simpa using h
  have hprev := st323_p480
  have hstep := st323_t481
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p482 : ((8250753793579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 482, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 482, stT323 (i+1))
      = (∑ i ∈ Finset.range 481, stT323 (i+1)) + stT323 482 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 481
    simpa using h
  have hprev := st323_p481
  have hstep := st323_t482
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p483 : ((1618892615567/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 483, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 483, stT323 (i+1))
      = (∑ i ∈ Finset.range 482, stT323 (i+1)) + stT323 483 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 482
    simpa using h
  have hprev := st323_p482
  have hstep := st323_t483
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p484 : ((1647268405373/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 484, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 484, stT323 (i+1))
      = (∑ i ∈ Finset.range 483, stT323 (i+1)) + stT323 484 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 483
    simpa using h
  have hprev := st323_p483
  have hstep := st323_t484
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p485 : ((1722892038717/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 485, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 485, stT323 (i+1))
      = (∑ i ∈ Finset.range 484, stT323 (i+1)) + stT323 485 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 484
    simpa using h
  have hprev := st323_p484
  have hstep := st323_t485
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p486 : ((906661991283/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 486, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 486, stT323 (i+1))
      = (∑ i ∈ Finset.range 485, stT323 (i+1)) + stT323 486 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 485
    simpa using h
  have hprev := st323_p485
  have hstep := st323_t486
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p487 : ((9400401874629/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 487, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 487, stT323 (i+1))
      = (∑ i ∈ Finset.range 486, stT323 (i+1)) + stT323 487 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 486
    simpa using h
  have hprev := st323_p486
  have hstep := st323_t487
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p488 : ((1894995390741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 488, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 488, stT323 (i+1))
      = (∑ i ∈ Finset.range 487, stT323 (i+1)) + stT323 488 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 487
    simpa using h
  have hprev := st323_p487
  have hstep := st323_t488
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p489 : ((1851976534877/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 489, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 489, stT323 (i+1))
      = (∑ i ∈ Finset.range 488, stT323 (i+1)) + stT323 489 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 488
    simpa using h
  have hprev := st323_p488
  have hstep := st323_t489
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p490 : ((8846494786343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 490, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 490, stT323 (i+1))
      = (∑ i ∈ Finset.range 489, stT323 (i+1)) + stT323 490 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 489
    simpa using h
  have hprev := st323_p489
  have hstep := st323_t490
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p491 : ((8408433629011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 491, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 491, stT323 (i+1))
      = (∑ i ∈ Finset.range 490, stT323 (i+1)) + stT323 491 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 490
    simpa using h
  have hprev := st323_p490
  have hstep := st323_t491
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p492 : ((8128269431621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 492, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 492, stT323 (i+1))
      = (∑ i ∈ Finset.range 491, stT323 (i+1)) + stT323 492 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 491
    simpa using h
  have hprev := st323_p491
  have hstep := st323_t492
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p493 : ((8121637615571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 493, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 493, stT323 (i+1))
      = (∑ i ∈ Finset.range 492, stT323 (i+1)) + stT323 493 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 492
    simpa using h
  have hprev := st323_p492
  have hstep := st323_t493
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p494 : ((2097562025307/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 494, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 494, stT323 (i+1))
      = (∑ i ∈ Finset.range 493, stT323 (i+1)) + stT323 494 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 493
    simpa using h
  have hprev := st323_p493
  have hstep := st323_t494
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p495 : ((220561162911/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 495, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 495, stT323 (i+1))
      = (∑ i ∈ Finset.range 494, stT323 (i+1)) + stT323 495 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 494
    simpa using h
  have hprev := st323_p494
  have hstep := st323_t495
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p496 : ((9240350548761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 496, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 496, stT323 (i+1))
      = (∑ i ∈ Finset.range 495, stT323 (i+1)) + stT323 496 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 495
    simpa using h
  have hprev := st323_p495
  have hstep := st323_t496
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p497 : ((1184158062791/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 497, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 497, stT323 (i+1))
      = (∑ i ∈ Finset.range 496, stT323 (i+1)) + stT323 497 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 496
    simpa using h
  have hprev := st323_p496
  have hstep := st323_t497
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p498 : ((2356770545667/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 498, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 498, stT323 (i+1))
      = (∑ i ∈ Finset.range 497, stT323 (i+1)) + stT323 498 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 497
    simpa using h
  have hprev := st323_p497
  have hstep := st323_t498
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p499 : ((912153988547/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 499, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 499, stT323 (i+1))
      = (∑ i ∈ Finset.range 498, stT323 (i+1)) + stT323 499 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 498
    simpa using h
  have hprev := st323_p498
  have hstep := st323_t499
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_p500 : ((135640032719/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 500, stT323 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 500, stT323 (i+1))
      = (∑ i ∈ Finset.range 499, stT323 (i+1)) + stT323 500 := by
    have h := Finset.sum_range_succ (fun i => stT323 (i+1)) 499
    simpa using h
  have hprev := st323_p499
  have hstep := st323_t500
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st323_s500 :
    |Real.sin (((323 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((3441/250000 : ℚ) : ℝ))
      - ((172207/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 1855327/2500000) (δ := 253/15625000) (ψ := 3441/250000) 323 319
    (log_br_500).1 (log_br_500).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 323`** (evaluated boundary). -/
theorem station_323_sign : hardyG ((((323:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 323 500 (by norm_num) (by norm_num)
    ((3441/250000 : ℚ) : ℝ)
  have hchain := st323_p500
  have hbridge : (∑ i ∈ Finset.range 500, stT323 (i+1))
      = ∑ i ∈ Finset.range 500,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((323 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((3441/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_500
  have hsh := rpow_half_shifts (N := 500) (by norm_num)
  have hcosb := abs_le.mp st323_c500
  have hsinb := abs_le.mp st323_s500
  have hbdy_lo : ((-24669522997127/2086585000000000 : ℚ) : ℝ)
      ≤ ((500:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((323 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((3441/250000 : ℚ) : ℝ))) / 2
          - ((((323:ℕ)):ℝ))
            * Real.sin (((323 : ℕ) : ℝ) * Real.log ((500 : ℕ)) - ((3441/250000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((323:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((323:ℝ) * Real.log (500:ℝ) - ((3441/250000 : ℚ) : ℝ))) / 2
        - ((323:ℝ)) * Real.sin ((323:ℝ) * Real.log (500:ℝ) - ((3441/250000 : ℚ) : ℝ))
        ≥ ((-110325361/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (500:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((323:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-110325361/2000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (500:ℝ) * (223607/5000000)
          * ((-110325361/2000000 : ℚ) : ℝ)
        ≤ (500:ℝ) * ((500:ℝ) ^ (-(1/2:ℝ)))
          * ((-110325361/2000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((500:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((323:ℕ)):ℝ))+1) * (((((323:ℕ)):ℝ))+2) / 8
        * (((500:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((500:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((80957585171/100000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((135640032719/156250000000 : ℚ) : ℝ) + ((-24669522997127/2086585000000000 : ℚ) : ℝ)
      - ((80957585171/100000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((3441/250000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((323:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((3441/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((323:ℕ)):ℝ)))).re
      - Real.sin ((3441/250000 : ℚ) : ℝ)
        * (riemannZeta (line ((((323:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((323:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((323:ℕ)):ℝ))
      = (((((323:ℕ)):ℝ)) * (Real.log ((((323:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((323:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_323
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
  have hθwin : |(((3441/250000 : ℚ) : ℝ) + ((76:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((323:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((323:ℕ)):ℝ)))
    (φ := ((3441/250000 : ℚ) : ℝ) + ((76:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((3441/250000 : ℚ) : ℝ) + ((76:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((3441/250000 : ℚ)) : ℝ) - Real.pi) + ((76:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((3441/250000 : ℚ)) : ℝ) - Real.pi) 76).1,
    (cos_sin_shift ((((3441/250000 : ℚ)) : ℝ) - Real.pi) 76).2]
  exact cos_sin_flip ((3441/250000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_323_sign
end AxiomAudit
