import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPLog500Table
import RequestProject.DVPSqrt500Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 289` (rung-290.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT289 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((289 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-30537/500000 : ℚ) : ℝ))

theorem st289_c1 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((124767/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 30537/2000000) (δ := 1/1000000000) (ψ := -30537/500000) 289 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t1 : ((249509/250000 : ℚ) : ℝ) ≤ stT289 1 := by
  have hc : ((249509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((249509/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((249509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c2 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((24273/31250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -425831/2500000) (δ := 3643/250000000) (ψ := -30537/500000) 289 32
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t2 : ((1372911297653/2500000000000 : ℚ) : ℝ) ≤ stT289 2 := by
  have hc : ((194159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1372911297653/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((194159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c3 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-966607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7206091/10000000) (δ := 3617/250000000) (ψ := -30537/500000) 289 51
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t3 : ((-5581285764621/10000000000000 : ℚ) : ℝ) ≤ stT289 3 := by
  have hc : ((-966707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5581285764621/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-966707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c4 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((36637/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27807/78125) (δ := 14561/1000000000) (ψ := -30537/500000) 289 64
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t4 : ((9153/125000 : ℚ) : ℝ) ≤ stT289 4 := by
  have hc : ((9153/62500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9153/125000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((9153/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c5 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((194599/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 291161/5000000) (δ := 1447/100000000) (ψ := -30537/500000) 289 74
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t5 : ((174036711233/400000000000 : ℚ) : ℝ) ≤ stT289 5 := by
  have hc : ((194579/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174036711233/400000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((194579/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c6 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-442749/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 66459/100000) (δ := 1459/100000000) (ψ := -30537/500000) 289 82
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t6 : ((-1807719389917/5000000000000 : ℚ) : ℝ) ≤ stT289 6 := by
  have hc : ((-442799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1807719389917/5000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-442799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c7 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-124559/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3821963/5000000) (δ := 2911/200000000) (ψ := -30537/500000) 289 90
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t7 : ((-188334418847/500000000000 : ℚ) : ℝ) ≤ stT289 7 := by
  have hc : ((-249143/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-188334418847/500000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-249143/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c8 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-560767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5415269/10000000) (δ := 907/62500000) (ψ := -30537/500000) 289 96
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t8 : ((-991482173989/5000000000000 : ℚ) : ℝ) ≤ stT289 8 := by
  have hc : ((-560867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-991482173989/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-560867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c9 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((897269/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 285783/2500000) (δ := 911/62500000) (ψ := -30537/500000) 289 101
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t9 : ((2990563034277/10000000000000 : ℚ) : ℝ) ≤ stT289 9 := by
  have hc : ((897169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2990563034277/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((897169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c10 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((436497/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1273723/10000000) (δ := 727/50000000) (ψ := -30537/500000) 289 106
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t10 : ((1380166309819/5000000000000 : ℚ) : ℝ) ≤ stT289 10 := by
  have hc : ((436447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1380166309819/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((436447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c11 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-40697/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1189011/2500000) (δ := 14591/1000000000) (ψ := -30537/500000) 289 110
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t11 : ((-122743783383/1250000000000 : ℚ) : ℝ) ≤ stT289 11 := by
  have hc : ((-81419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122743783383/1250000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-81419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c12 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-338361/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4789927/10000000) (δ := 14483/1000000000) (ψ := -30537/500000) 289 114
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t12 : ((-30532905271/312500000000 : ℚ) : ℝ) ≤ stT289 12 := by
  have hc : ((-338461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30532905271/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-338461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c13 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((498219/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8443/400000) (δ := 14549/1000000000) (ψ := -30537/500000) 289 118
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t13 : ((2763343443/10000000000 : ℚ) : ℝ) ≤ stT289 13 := by
  have hc : ((498169/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2763343443/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((498169/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c14 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-790993/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1241613/2000000) (δ := 1447/100000000) (ψ := -30537/500000) 289 121
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t14 : ((-2114285436009/10000000000000 : ℚ) : ℝ) ≤ stT289 14 := by
  have hc : ((-791093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2114285436009/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-791093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c15 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-454269/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3388209/5000000) (δ := 1813/125000000) (ψ := -30537/500000) 289 125
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t15 : ((-1173046660491/5000000000000 : ℚ) : ℝ) ≤ stT289 15 := by
  have hc : ((-454319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1173046660491/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-454319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c16 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-243239/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7271241/10000000) (δ := 731/50000000) (ψ := -30537/500000) 289 128
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t16 : ((-9502503801/39062500000 : ℚ) : ℝ) ≤ stT289 16 := by
  have hc : ((-15204/15625 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9502503801/39062500000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-15204/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c17 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-228601/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2557053/5000000) (δ := 2927/200000000) (ψ := -30537/500000) 289 130
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t17 : ((-554560303407/5000000000000 : ℚ) : ℝ) ≤ stT289 17 := by
  have hc : ((-228651/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554560303407/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-228651/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c18 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((959623/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17821/250000) (δ := 3639/250000000) (ψ := -30537/500000) 289 133
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t18 : ((1130808410253/5000000000000 : ℚ) : ℝ) ≤ stT289 18 := by
  have hc : ((959523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1130808410253/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((959523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c19 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-233291/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1386957/2000000) (δ := 3633/250000000) (ψ := -30537/500000) 289 135
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t19 : ((-66907970991/312500000000 : ℚ) : ℝ) ≤ stT289 19 := by
  have hc : ((-58329/62500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66907970991/312500000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-58329/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c20 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((15677/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -625939/2000000) (δ := 57/3906250) (ψ := -30537/500000) 289 138
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t20 : ((4380455253/62500000000 : ℚ) : ℝ) ≤ stT289 20 := by
  have hc : ((1959/6250 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4380455253/62500000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((1959/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c21 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((240117/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 352649/5000000) (δ := 14607/1000000000) (ψ := -30537/500000) 289 140
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t21 : ((65490435047/312500000000 : ℚ) : ℝ) ≤ stT289 21 := by
  have hc : ((60023/62500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65490435047/312500000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((60023/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c22 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((399313/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2900071/10000000) (δ := 7241/500000000) (ψ := -30537/500000) 289 142
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t22 : ((851124910491/10000000000000 : ℚ) : ℝ) ≤ stT289 22 := by
  have hc : ((399213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((851124910491/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((399213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c23 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((65099/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360057/1000000) (δ := 3617/250000000) (ψ := -30537/500000) 289 144
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t23 : ((16954566507/625000000000 : ℚ) : ℝ) ≤ stT289 23 := by
  have hc : ((65049/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16954566507/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((65049/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c24 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((386851/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 586791/2000000) (δ := 293/20000000) (ψ := -30537/500000) 289 146
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t24 : ((789451997991/10000000000000 : ℚ) : ℝ) ≤ stT289 24 := by
  have hc : ((386751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((789451997991/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((386751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c25 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((919193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1011923/10000000) (δ := 113/7812500) (ψ := -30537/500000) 289 148
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t25 : ((919093/5000000 : ℚ) : ℝ) ≤ stT289 25 := by
  have hc : ((919093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((919093/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((919093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c26 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((33861/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258381/1250000) (δ := 581/40000000) (ψ := -30537/500000) 289 150
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t26 : ((1037454169/7812500000 : ℚ) : ℝ) ≤ stT289 26 := by
  have hc : ((2116/3125 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1037454169/7812500000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((2116/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c27 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-158567/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -776951/1250000) (δ := 1461/100000000) (ψ := -30537/500000) 289 152
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t27 : ((-305200840087/2000000000000 : ℚ) : ℝ) ≤ stT289 27 := by
  have hc : ((-158587/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305200840087/2000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-158587/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c28 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-84611/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1088023/2500000) (δ := 14603/1000000000) (ψ := -30537/500000) 289 153
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t28 : ((-159994305003/5000000000000 : ℚ) : ℝ) ≤ stT289 28 := by
  have hc : ((-84661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-159994305003/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-84661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c29 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((387479/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -171037/1000000) (δ := 14489/1000000000) (ψ := -30537/500000) 289 155
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t29 : ((719437443837/5000000000000 : ℚ) : ℝ) ≤ stT289 29 := by
  have hc : ((387429/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((719437443837/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((387429/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c30 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-237977/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7075501/10000000) (δ := 7311/500000000) (ψ := -30537/500000) 289 156
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t30 : ((-108632561871/625000000000 : ℚ) : ℝ) ≤ stT289 30 := by
  have hc : ((-119001/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108632561871/625000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-119001/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c31 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((483209/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -649723/10000000) (δ := 1817/125000000) (ψ := -30537/500000) 289 158
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t31 : ((867779171427/5000000000000 : ℚ) : ℝ) ≤ stT289 31 := by
  have hc : ((483159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((867779171427/5000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((483159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c32 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-873089/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6580749/10000000) (δ := 91/6250000) (ψ := -30537/500000) 289 159
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t32 : ((-1543594698963/10000000000000 : ℚ) : ℝ) ≤ stT289 32 := by
  have hc : ((-873189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1543594698963/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-873189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c33 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((50529/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -325337/1250000) (δ := 14557/1000000000) (ψ := -30537/500000) 289 161
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t33 : ((10992782843/125000000000 : ℚ) : ℝ) ≤ stT289 33 := by
  have hc : ((50519/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10992782843/125000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((50519/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c34 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((264363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3258133/10000000) (δ := 2893/200000000) (ψ := -30537/500000) 289 162
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t34 : ((90641416211/2000000000000 : ℚ) : ℝ) ≤ stT289 34 := by
  have hc : ((264263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90641416211/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((264263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c35 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-193489/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288573/400000) (δ := 3631/250000000) (ψ := -30537/500000) 289 164
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t35 : ((-327090004281/2000000000000 : ℚ) : ℝ) ≤ stT289 35 := by
  have hc : ((-193509/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327090004281/2000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-193509/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c36 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((516939/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2568813/10000000) (δ := 14517/1000000000) (ψ := -30537/500000) 289 165
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t36 : ((430698994387/5000000000000 : ℚ) : ℝ) ≤ stT289 36 := by
  have hc : ((516839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((430698994387/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((516839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c37 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((41051/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1519001/10000000) (δ := 1461/100000000) (ψ := -30537/500000) 289 166
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t37 : ((33739586247/250000000000 : ℚ) : ℝ) ≤ stT289 37 := by
  have hc : ((20523/25000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33739586247/250000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((20523/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c38 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-444601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5078813/10000000) (δ := 73/5000000) (ψ := -30537/500000) 289 167
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t38 : ((-144280126543/2000000000000 : ℚ) : ℝ) ≤ stT289 38 := by
  have hc : ((-444701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144280126543/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-444701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c39 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-993547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1513963/2000000) (δ := 2903/200000000) (ψ := -30537/500000) 289 169
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t39 : ((-795554527727/5000000000000 : ℚ) : ℝ) ≤ stT289 39 := by
  have hc : ((-993647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-795554527727/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-993647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c40 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-410927/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1246417/2500000) (δ := 14481/1000000000) (ψ := -30537/500000) 289 170
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t40 : ((-649890819753/10000000000000 : ℚ) : ℝ) ≤ stT289 40 := by
  have hc : ((-411027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-649890819753/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-411027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c41 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((416421/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -713307/2500000) (δ := 7287/500000000) (ψ := -30537/500000) 289 171
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t41 : ((650183909577/10000000000000 : ℚ) : ℝ) ≤ stT289 41 := by
  have hc : ((416321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650183909577/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((416321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c42 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((895933/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -46027/400000) (δ := 14467/1000000000) (ψ := -30537/500000) 289 172
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t42 : ((1382299881489/10000000000000 : ℚ) : ℝ) ≤ stT289 42 := by
  have hc : ((895833/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1382299881489/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((895833/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c43 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((62399/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35537/2500000) (δ := 14459/1000000000) (ψ := -30537/500000) 289 173
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t43 : ((76118406287/500000000000 : ℚ) : ℝ) ≤ stT289 43 := by
  have hc : ((249571/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76118406287/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((249571/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c44 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((914049/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1044099/10000000) (δ := 14651/1000000000) (ψ := -30537/500000) 289 174
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t44 : ((344457324661/2500000000000 : ℚ) : ℝ) ≤ stT289 44 := by
  have hc : ((913949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((344457324661/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((913949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c45 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((808561/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1572733/10000000) (δ := 2909/200000000) (ψ := -30537/500000) 289 175
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t45 : ((1205181705771/10000000000000 : ℚ) : ℝ) ≤ stT289 45 := by
  have hc : ((808461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1205181705771/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((808461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c46 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((766251/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 69781/400000) (δ := 7269/500000000) (ψ := -30537/500000) 289 176
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t46 : ((1129627591269/10000000000000 : ℚ) : ℝ) ≤ stT289 46 := by
  have hc : ((766151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1129627591269/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((766151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c47 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((40403/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98429/625000) (δ := 3643/250000000) (ψ := -30537/500000) 289 177
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t47 : ((29463251151/250000000000 : ℚ) : ℝ) ≤ stT289 47 := by
  have hc : ((20199/25000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29463251151/250000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((20199/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c48 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((227117/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 538991/5000000) (δ := 14479/1000000000) (ψ := -30537/500000) 289 178
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t48 : ((655557831/5000000000 : ℚ) : ℝ) ≤ stT289 48 := by
  have hc : ((56773/62500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((655557831/5000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((56773/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c49 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((497143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267391/10000000) (δ := 14587/1000000000) (ψ := -30537/500000) 289 179
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t49 : ((710132644103/5000000000000 : ℚ) : ℝ) ≤ stT289 49 := by
  have hc : ((497093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((710132644103/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((497093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c50 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((471773/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -16881/200000) (δ := 14609/1000000000) (ψ := -30537/500000) 289 180
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t50 : ((667116798999/5000000000000 : ℚ) : ℝ) ≤ stT289 50 := by
  have hc : ((471723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667116798999/5000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((471723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c51 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((62329/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1122317/5000000) (δ := 14601/1000000000) (ψ := -30537/500000) 289 181
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t51 : ((2181601233/25000000000 : ℚ) : ℝ) ≤ stT289 51 := by
  have hc : ((62319/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2181601233/25000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((62319/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c52 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((397/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196151/500000) (δ := 913/62500000) (ψ := -30537/500000) 289 182
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t52 : ((515871/2500000000 : ℚ) : ℝ) ≤ stT289 52 := by
  have hc : ((93/62500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((515871/2500000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((93/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c53 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-350453/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5868659/10000000) (δ := 2903/200000000) (ψ := -30537/500000) 289 183
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t53 : ((-240726511909/2500000000000 : ℚ) : ℝ) ≤ stT289 53 := by
  have hc : ((-350503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-240726511909/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-350503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c54 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-498107/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7636383/10000000) (δ := 1811/125000000) (ψ := -30537/500000) 289 183
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t54 : ((-169476498499/1250000000000 : ℚ) : ℝ) ≤ stT289 54 := by
  have hc : ((-498157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169476498499/1250000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-498157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c55 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-482461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1037129/2000000) (δ := 14623/1000000000) (ψ := -30537/500000) 289 184
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t55 : ((-1626713131/25000000000 : ℚ) : ℝ) ≤ stT289 55 := by
  have hc : ((-482561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1626713131/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-482561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c56 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((8463/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156003/625000) (δ := 1463/100000000) (ψ := -30537/500000) 289 185
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t56 : ((90456557599/1250000000000 : ℚ) : ℝ) ≤ stT289 56 := by
  have hc : ((135383/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90456557599/1250000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((135383/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c57 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((197131/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84791/2000000) (δ := 7283/500000000) (ψ := -30537/500000) 289 186
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t57 : ((65269956763/500000000000 : ℚ) : ℝ) ≤ stT289 57 := by
  have hc : ((197111/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65269956763/500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((197111/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c58 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((1797/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1783171/5000000) (δ := 3661/250000000) (ψ := -30537/500000) 289 187
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t58 : ((1178967339/62500000000 : ℚ) : ℝ) ≤ stT289 58 := by
  have hc : ((7183/50000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1178967339/62500000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((7183/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c59 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-931547/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3461801/5000000) (δ := 1819/125000000) (ψ := -30537/500000) 289 188
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t59 : ((-121290191283/1000000000000 : ℚ) : ℝ) ≤ stT289 59 := by
  have hc : ((-931647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121290191283/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-931647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c60 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-494287/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 652441/1250000) (δ := 3613/250000000) (ψ := -30537/500000) 289 188
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t60 : ((-127650229013/2000000000000 : ℚ) : ℝ) ≤ stT289 60 := by
  have hc : ((-494387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127650229013/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-494387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c61 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((208897/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 45437/312500) (δ := 7229/500000000) (ψ := -30537/500000) 289 189
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t61 : ((2089320507/19531250000 : ℚ) : ℝ) ≤ stT289 61 := by
  have hc : ((26109/31250 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2089320507/19531250000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((26109/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c62 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((538359/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313221/1250000) (δ := 7233/500000000) (ψ := -30537/500000) 289 190
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t62 : ((683589468259/10000000000000 : ℚ) : ℝ) ≤ stT289 62 := by
  have hc : ((538259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((683589468259/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((538259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c63 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-177379/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3326721/5000000) (δ := 14573/1000000000) (ψ := -30537/500000) 289 191
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t63 : ((-111750903459/1000000000000 : ℚ) : ℝ) ≤ stT289 63 := by
  have hc : ((-177399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111750903459/1000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-177399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c64 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-156849/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 147647/312500) (δ := 1463/100000000) (ψ := -30537/500000) 289 191
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t64 : ((-196123906899/5000000000000 : ℚ) : ℝ) ≤ stT289 64 := by
  have hc : ((-156899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-196123906899/5000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-156899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c65 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((498091/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109263/5000000) (δ := 729/50000000) (ψ := -30537/500000) 289 192
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t65 : ((617743660227/5000000000000 : ℚ) : ℝ) ≤ stT289 65 := by
  have hc : ((498041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((617743660227/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((498041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c66 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-3298/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4458669/10000000) (δ := 3629/250000000) (ψ := -30537/500000) 289 193
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t66 : ((-12996739119/500000000000 : ℚ) : ℝ) ≤ stT289 66 := by
  have hc : ((-52793/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12996739119/500000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-52793/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c67 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-104619/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3203107/5000000) (δ := 14487/1000000000) (ψ := -30537/500000) 289 193
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t67 : ((-51131112157/500000000000 : ℚ) : ℝ) ≤ stT289 67 := by
  have hc : ((-209263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51131112157/500000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-209263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c68 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((211699/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17527/125000) (δ := 14609/1000000000) (ψ := -30537/500000) 289 194
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t68 : ((64173100743/625000000000 : ℚ) : ℝ) ≤ stT289 68 := by
  have hc : ((105837/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64173100743/625000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((105837/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c69 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((67477/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -375817/1000000) (δ := 14501/1000000000) (ψ := -30537/500000) 289 195
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t69 : ((40556170233/5000000000000 : ℚ) : ℝ) ≤ stT289 69 := by
  have hc : ((67377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40556170233/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((67377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c70 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-441981/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3318833/5000000) (δ := 7251/500000000) (ψ := -30537/500000) 289 195
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t70 : ((-528328270099/5000000000000 : ℚ) : ℝ) ≤ stT289 70 := by
  have hc : ((-442031/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528328270099/5000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-442031/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c71 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((89101/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 294519/2500000) (δ := 7247/500000000) (ψ := -30537/500000) 289 196
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t71 : ((105731506071/1000000000000 : ℚ) : ℝ) ≤ stT289 71 := by
  have hc : ((89091/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105731506071/1000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((89091/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c72 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-39561/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -884957/2000000) (δ := 1827/125000000) (ψ := -30537/500000) 289 197
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t72 : ((-2915417717/125000000000 : ℚ) : ℝ) ≤ stT289 72 := by
  have hc : ((-39581/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2915417717/125000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-39581/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c73 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-15041/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2770437/5000000) (δ := 3629/250000000) (ψ := -30537/500000) 289 197
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t73 : ((-8803546461/125000000000 : ℚ) : ℝ) ≤ stT289 73 := by
  have hc : ((-30087/50000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8803546461/125000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-30087/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c74 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((495463/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337043/10000000) (δ := 14623/1000000000) (ψ := -30537/500000) 289 198
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t74 : ((143976430647/1250000000000 : ℚ) : ℝ) ≤ stT289 74 := by
  have hc : ((495413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((143976430647/1250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((495413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c75 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-411857/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6346817/10000000) (δ := 14473/1000000000) (ψ := -30537/500000) 289 199
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t75 : ((-475629424807/5000000000000 : ℚ) : ℝ) ≤ stT289 75 := by
  have hc : ((-411907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475629424807/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-411907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c76 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((277951/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80571/250000) (δ := 14473/1000000000) (ψ := -30537/500000) 289 199
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t76 : ((159358384689/5000000000000 : ℚ) : ℝ) ≤ stT289 76 := by
  have hc : ((277851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159358384689/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((277851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c77 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((217/625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3040531/10000000) (δ := 7233/500000000) (ψ := -30537/500000) 289 200
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t77 : ((791113791/20000000000 : ℚ) : ℝ) ≤ stT289 77 := by
  have hc : ((3471/10000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((791113791/20000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((3471/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c78 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-40439/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 98159/156250) (δ := 14637/1000000000) (ψ := -30537/500000) 289 200
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t78 : ((-5724231429/62500000000 : ℚ) : ℝ) ≤ stT289 78 := by
  have hc : ((-10111/12500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5724231429/62500000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-10111/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c79 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((199213/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11093/500000) (δ := 2909/200000000) (ψ := -30537/500000) 289 201
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t79 : ((224109454791/2000000000000 : ℚ) : ℝ) ≤ stT289 79 := by
  have hc : ((199193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((224109454791/2000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((199193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c80 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-114891/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6841641/10000000) (δ := 14651/1000000000) (ψ := -30537/500000) 289 202
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t80 : ((-128466019719/1250000000000 : ℚ) : ℝ) ≤ stT289 80 := by
  have hc : ((-229807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128466019719/1250000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-229807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c81 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((65739/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 133351/625000) (δ := 1819/125000000) (ψ := -30537/500000) 289 202
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t81 : ((73032214919/1000000000000 : ℚ) : ℝ) ≤ stT289 81 := by
  have hc : ((65729/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73032214919/1000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((65729/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c82 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-76951/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11773/25000) (δ := 14559/1000000000) (ψ := -30537/500000) 289 203
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t82 : ((-1328216069/39062500000 : ℚ) : ℝ) ≤ stT289 82 := by
  have hc : ((-4811/15625 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1328216069/39062500000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-4811/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c83 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-48589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4048511/10000000) (δ := 909/62500000) (ψ := -30537/500000) 289 203
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t83 : ((-53443140027/10000000000000 : ℚ) : ℝ) ≤ stT289 83 := by
  have hc : ((-48689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53443140027/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-48689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c84 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((71973/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -751671/2500000) (δ := 29037/1000000000) (ψ := -30537/500000) 289 204
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t84 : ((78507126817/2000000000000 : ℚ) : ℝ) ≤ stT289 84 := by
  have hc : ((71953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78507126817/2000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((71953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c85 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-120509/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2771853/5000000) (δ := 14637/1000000000) (ψ := -30537/500000) 289 204
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t85 : ((-130732141437/2000000000000 : ℚ) : ℝ) ≤ stT289 85 := by
  have hc : ((-120529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-130732141437/2000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-120529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c86 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((154813/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1713897/10000000) (δ := 1453/100000000) (ψ := -30537/500000) 289 205
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t86 : ((166917471311/2000000000000 : ℚ) : ℝ) ≤ stT289 86 := by
  have hc : ((154793/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166917471311/2000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((154793/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c87 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-110523/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6638853/10000000) (δ := 1463/100000000) (ψ := -30537/500000) 289 205
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t87 : ((-237013093023/2500000000000 : ℚ) : ℝ) ≤ stT289 87 := by
  have hc : ((-221071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-237013093023/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-221071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c88 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((947731/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -405937/5000000) (δ := 181/12500000) (ψ := -30537/500000) 289 206
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t88 : ((1010177488893/10000000000000 : ℚ) : ℝ) ≤ stT289 88 := by
  have hc : ((947631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1010177488893/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((947631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c89 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-97991/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1470403/2000000) (δ := 729/50000000) (ψ := -30537/500000) 289 206
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t89 : ((-51940431999/500000000000 : ℚ) : ℝ) ≤ stT289 89 := by
  have hc : ((-98001/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51940431999/500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-98001/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c90 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((993589/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283239/10000000) (δ := 3647/250000000) (ψ := -30537/500000) 289 207
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t90 : ((261807201747/2500000000000 : ℚ) : ℝ) ≤ stT289 90 := by
  have hc : ((993489/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261807201747/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((993489/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c91 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-998111/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7700277/10000000) (δ := 5803/200000000) (ψ := -30537/500000) 289 207
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t91 : ((-209281923627/2000000000000 : ℚ) : ℝ) ≤ stT289 91 := by
  have hc : ((-998211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209281923627/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-998211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c92 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((999007/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111447/10000000) (δ := 2919/200000000) (ψ := -30537/500000) 289 208
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t92 : ((260358117201/2500000000000 : ℚ) : ℝ) ≤ stT289 92 := by
  have hc : ((998907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260358117201/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((998907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c93 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-99809/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1924857/2500000) (δ := 2899/200000000) (ψ := -30537/500000) 289 208
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t93 : ((-12938438961/125000000000 : ℚ) : ℝ) ≤ stT289 93 := by
  have hc : ((-99819/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12938438961/125000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-99819/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c94 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((496841/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281181/10000000) (δ := 7251/500000000) (ψ := -30537/500000) 289 209
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t94 : ((512400670011/5000000000000 : ℚ) : ℝ) ≤ stT289 94 := by
  have hc : ((496791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((512400670011/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((496791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c95 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-196177/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3682193/5000000) (δ := 14501/1000000000) (ψ := -30537/500000) 289 209
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t95 : ((-201294001863/2000000000000 : ℚ) : ℝ) ≤ stT289 95 := by
  have hc : ((-196197/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-201294001863/2000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-196197/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c96 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((951959/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -778063/10000000) (δ := 7247/500000000) (ψ := -30537/500000) 289 210
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t96 : ((48574316629/500000000000 : ℚ) : ℝ) ≤ stT289 96 := by
  have hc : ((951859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48574316629/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((951859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c97 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-112119/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 335453/500000) (δ := 7247/500000000) (ψ := -30537/500000) 289 210
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t97 : ((-227704764261/2500000000000 : ℚ) : ℝ) ≤ stT289 97 := by
  have hc : ((-224263/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-227704764261/2500000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-224263/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c98 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((160963/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -794291/5000000) (δ := 14487/1000000000) (ψ := -30537/500000) 289 211
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t98 : ((20322111667/250000000000 : ℚ) : ℝ) ≤ stT289 98 := by
  have hc : ((160943/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20322111667/250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((160943/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c99 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-665239/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5746527/10000000) (δ := 14487/1000000000) (ψ := -30537/500000) 289 211
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t99 : ((-334345488941/5000000000000 : ℚ) : ℝ) ≤ stT289 99 := by
  have hc : ((-665339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-334345488941/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-665339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c100 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((94259/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1350047/5000000) (δ := 457/31250000) (ψ := -30537/500000) 289 212
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t100 : ((94238905761/2000000000000 : ℚ) : ℝ) ≤ stT289 100 := by
  have hc : ((94239/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94238905761/2000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((94239/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c101 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-111471/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 448907/1000000) (δ := 457/31250000) (ψ := -30537/500000) 289 212
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t101 : ((-55483816399/2500000000000 : ℚ) : ℝ) ≤ stT289 101 := by
  have hc : ((-111521/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).2
  have h0 : (0:ℝ) ≤ ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55483816399/2500000000000 : ℚ) : ℝ)
      = ((497519/5000000 : ℚ) : ℝ) * ((-111521/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c102 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-69391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4100607/10000000) (δ := 1809/125000000) (ψ := -30537/500000) 289 213
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t102 : ((-17201593667/2500000000000 : ℚ) : ℝ) ≤ stT289 102 := by
  have hc : ((-69491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17201593667/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-69491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c103 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((477/1250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117927/400000) (δ := 3643/250000000) (ψ := -30537/500000) 289 213
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t103 : ((751806027/20000000000 : ℚ) : ℝ) ≤ stT289 103 := by
  have hc : ((763/2000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((751806027/20000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((763/2000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c104 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-6749/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1155813/2000000) (δ := 7269/500000000) (ψ := -30537/500000) 289 214
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t104 : ((-26475687/400000000 : ℚ) : ℝ) ≤ stT289 104 := by
  have hc : ((-27/40 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26475687/400000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-27/40 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c105 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((449359/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1134899/10000000) (δ := 7319/500000000) (ψ := -30537/500000) 289 214
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t105 : ((4384806531/50000000000 : ℚ) : ℝ) ≤ stT289 105 := by
  have hc : ((449309/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4384806531/50000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((449309/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c106 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-998663/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241397/312500) (δ := 7229/500000000) (ψ := -30537/500000) 289 215
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t106 : ((-485042259609/5000000000000 : ℚ) : ℝ) ≤ stT289 106 := by
  have hc : ((-998763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485042259609/5000000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-998763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c107 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((930057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -940573/10000000) (δ := 2929/200000000) (ψ := -30537/500000) 289 215
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t107 : ((56188931897/625000000000 : ℚ) : ℝ) ≤ stT289 107 := by
  have hc : ((929957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56188931897/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((929957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c108 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-337649/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5780411/10000000) (δ := 2929/200000000) (ψ := -30537/500000) 289 215
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t108 : ((-324951200449/5000000000000 : ℚ) : ℝ) ≤ stT289 108 := by
  have hc : ((-337699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324951200449/5000000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-337699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c109 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((130169/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3268559/10000000) (δ := 1819/125000000) (ψ := -30537/500000) 289 216
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t109 : ((62315680647/2500000000000 : ℚ) : ℝ) ≤ stT289 109 := by
  have hc : ((130119/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62315680647/2500000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((130119/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c110 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((236661/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 416209/1250000) (δ := 3613/250000000) (ψ := -30537/500000) 289 216
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t110 : ((112775962091/5000000000000 : ℚ) : ℝ) ≤ stT289 110 := by
  have hc : ((236561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112775962091/5000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((236561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c111 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-692609/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5839739/10000000) (δ := 3661/250000000) (ψ := -30537/500000) 289 217
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t111 : ((-328745144511/5000000000000 : ℚ) : ℝ) ≤ stT289 111 := by
  have hc : ((-692709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-328745144511/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-692709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c112 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((967403/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25603/400000) (δ := 14459/1000000000) (ψ := -30537/500000) 289 217
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t112 : ((914015245033/10000000000000 : ℚ) : ℝ) ≤ stT289 112 := by
  have hc : ((967303/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((914015245033/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((967303/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c113 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-475143/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7062377/10000000) (δ := 3661/250000000) (ψ := -30537/500000) 289 217
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t113 : ((-447024034153/5000000000000 : ℚ) : ℝ) ≤ stT289 113 := by
  have hc : ((-475193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-447024034153/5000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-475193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c114 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((612189/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2279927/10000000) (δ := 14567/1000000000) (ψ := -30537/500000) 289 218
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t114 : ((114654675213/2000000000000 : ℚ) : ℝ) ≤ stT289 114 := by
  have hc : ((612089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114654675213/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((612089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c115 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-2063/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4030171/10000000) (δ := 14467/1000000000) (ψ := -30537/500000) 289 218
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t115 : ((-96421017/25000000000 : ℚ) : ℝ) ≤ stT289 115 := by
  have hc : ((-517/12500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-96421017/25000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-517/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c116 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-281561/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5422387/10000000) (δ := 7287/500000000) (ψ := -30537/500000) 289 219
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t116 : ((-261469336447/5000000000000 : ℚ) : ℝ) ≤ stT289 116 := by
  have hc : ((-281611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-261469336447/5000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-281611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c117 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((475897/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 48713/625000) (δ := 14529/1000000000) (ψ := -30537/500000) 289 219
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t117 : ((879841103/10000000000 : ℚ) : ℝ) ≤ stT289 117 := by
  have hc : ((475847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((879841103/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((475847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c118 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-466121/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6928389/10000000) (δ := 7237/500000000) (ψ := -30537/500000) 289 219
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t118 : ((-17165814733/200000000000 : ℚ) : ℝ) ≤ stT289 118 := by
  have hc : ((-466171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17165814733/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-466171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c119 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((119369/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2682541/10000000) (δ := 14581/1000000000) (ψ := -30537/500000) 289 220
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t119 : ((3418825191/78125000000 : ℚ) : ℝ) ≤ stT289 119 := by
  have hc : ((7459/15625 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3418825191/78125000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((7459/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c120 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((223471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 672711/2000000) (δ := 7311/500000000) (ψ := -30537/500000) 289 220
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t120 : ((20390868477/1000000000000 : ℚ) : ℝ) ≤ stT289 120 := by
  have hc : ((223371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20390868477/1000000000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((223371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c121 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-824101/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -253941/400000) (δ := 2903/200000000) (ψ := -30537/500000) 289 221
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t121 : ((-749273711291/10000000000000 : ℚ) : ℝ) ≤ stT289 121 := by
  have hc : ((-824201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-749273711291/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-824201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c122 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((9871/10000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401989/10000000) (δ := 2923/200000000) (ψ := -30537/500000) 289 221
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t122 : ((893587359/10000000000 : ℚ) : ℝ) ≤ stT289 122 := by
  have hc : ((987/1000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((893587359/10000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((987/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c123 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-117441/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1373999/2500000) (δ := 3647/250000000) (ψ := -30537/500000) 289 221
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t123 : ((-10591105987/200000000000 : ℚ) : ℝ) ≤ stT289 123 := by
  have hc : ((-117461/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10591105987/200000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-117461/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c124 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-6921/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4361741/10000000) (δ := 913/62500000) (ψ := -30537/500000) 289 222
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t124 : ((-248753479/16000000000 : ℚ) : ℝ) ≤ stT289 124 := by
  have hc : ((-277/1600 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-248753479/16000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-277/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c125 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((209579/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 360381/2500000) (δ := 2899/200000000) (ψ := -30537/500000) 289 222
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t125 : ((93715377779/1250000000000 : ℚ) : ℝ) ≤ stT289 125 := by
  have hc : ((104777/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93715377779/1250000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((104777/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c126 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-965829/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1799637/2500000) (δ := 913/62500000) (ψ := -30537/500000) 289 222
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t126 : ((-860518134159/10000000000000 : ℚ) : ℝ) ≤ stT289 126 := by
  have hc : ((-965929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-860518134159/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-965929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c127 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((43641/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139899/500000) (δ := 14503/1000000000) (ψ := -30537/500000) 289 223
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t127 : ((9679057409/250000000000 : ℚ) : ℝ) ≤ stT289 127 := by
  have hc : ((43631/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9679057409/250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((43631/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c128 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((16431/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 717183/2500000) (δ := 14503/1000000000) (ψ := -30537/500000) 289 223
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t128 : ((14519546041/400000000000 : ℚ) : ℝ) ≤ stT289 128 := by
  have hc : ((16427/40000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14519546041/400000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((16427/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c129 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-483837/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -451037/625000) (δ := 14493/1000000000) (ψ := -30537/500000) 289 224
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t129 : ((-426038793037/5000000000000 : ℚ) : ℝ) ≤ stT289 129 := by
  have hc : ((-483887/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).2
  have h0 : (0:ℝ) ≤ ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426038793037/5000000000000 : ℚ) : ℝ)
      = ((880451/10000000 : ℚ) : ℝ) * ((-483887/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c130 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((793061/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1637447/10000000) (δ := 14493/1000000000) (ψ := -30537/500000) 289 224
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t130 : ((347736394369/5000000000000 : ℚ) : ℝ) ≤ stT289 130 := by
  have hc : ((792961/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((347736394369/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((792961/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c131 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((11197/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1949499/5000000) (δ := 14593/1000000000) (ψ := -30537/500000) 289 224
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t131 : ((1211936661/1250000000000 : ℚ) : ℝ) ≤ stT289 131 := by
  have hc : ((11097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).1
  have hw2 : ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((109213/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1211936661/1250000000000 : ℚ) : ℝ)
      = ((109213/1250000 : ℚ) : ℝ) * ((11097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c132 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-204087/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6314641/10000000) (δ := 14617/1000000000) (ψ := -30537/500000) 289 225
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t132 : ((-11103552473/156250000000 : ℚ) : ℝ) ≤ stT289 132 := by
  have hc : ((-12757/15625 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11103552473/156250000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-12757/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c133 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((235293/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -861789/10000000) (δ := 14617/1000000000) (ψ := -30537/500000) 289 225
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t133 : ((51000750053/625000000000 : ℚ) : ℝ) ≤ stT289 133 := by
  have hc : ((58817/62500 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51000750053/625000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((58817/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c134 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-30839/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910041/2000000) (δ := 14493/500000000) (ψ := -30537/500000) 289 225
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t134 : ((-53303308907/2500000000000 : ℚ) : ℝ) ≤ stT289 134 := by
  have hc : ((-61703/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53303308907/2500000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-61703/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c135 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-676947/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5786007/10000000) (δ := 14579/1000000000) (ψ := -30537/500000) 289 226
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t135 : ((-582709302161/10000000000000 : ℚ) : ℝ) ≤ stT289 135 := by
  have hc : ((-677047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-582709302161/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-677047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c136 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((245891/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -113471/2500000) (δ := 457/31250000) (ψ := -30537/500000) 289 226
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t136 : ((26353516009/312500000000 : ℚ) : ℝ) ≤ stT289 136 := by
  have hc : ((122933/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26353516009/312500000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((122933/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c137 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-356849/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4839223/10000000) (δ := 3631/250000000) (ψ := -30537/500000) 289 226
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t137 : ((-152481116871/5000000000000 : ℚ) : ℝ) ≤ stT289 137 := by
  have hc : ((-356949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152481116871/5000000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-356949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c138 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-624811/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1122843/2000000) (δ := 3643/250000000) (ψ := -30537/500000) 289 227
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t138 : ((-531959863127/10000000000000 : ℚ) : ℝ) ≤ stT289 138 := by
  have hc : ((-624911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-531959863127/10000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-624911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c139 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((987383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -99387/2500000) (δ := 1809/125000000) (ψ := -30537/500000) 289 227
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t139 : ((209350398301/2500000000000 : ℚ) : ℝ) ≤ stT289 139 := by
  have hc : ((987283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((209350398301/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((987283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c140 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-16763/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4781693/10000000) (δ := 3643/250000000) (ψ := -30537/500000) 289 227
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t140 : ((-22143061/781250000 : ℚ) : ℝ) ≤ stT289 140 := by
  have hc : ((-1048/3125 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22143061/781250000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-1048/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c141 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-33817/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1445987/2500000) (δ := 7319/500000000) (ψ := -30537/500000) 289 228
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t141 : ((-1780204059/31250000000 : ℚ) : ℝ) ≤ stT289 141 := by
  have hc : ((-16911/25000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1780204059/31250000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-16911/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c142 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((963461/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -84737/1250000) (δ := 7319/500000000) (ψ := -30537/500000) 289 228
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t142 : ((808434247341/10000000000000 : ℚ) : ℝ) ≤ stT289 142 := by
  have hc : ((963361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).1
  have hw2 : ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((839181/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((808434247341/10000000000000 : ℚ) : ℝ)
      = ((839181/10000000 : ℚ) : ℝ) * ((963361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c143 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-185059/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6863/15625) (δ := 7319/500000000) (ψ := -30537/500000) 289 228
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t143 : ((-154837917637/10000000000000 : ℚ) : ℝ) ≤ stT289 143 := by
  have hc : ((-185159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154837917637/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-185159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c144 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-808463/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -628083/1000000) (δ := 7273/500000000) (ψ := -30537/500000) 289 229
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t144 : ((-336901519521/5000000000000 : ℚ) : ℝ) ≤ stT289 144 := by
  have hc : ((-808563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).2
  have h0 : (0:ℝ) ≤ ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336901519521/5000000000000 : ℚ) : ℝ)
      = ((416667/5000000 : ℚ) : ℝ) * ((-808563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c145 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((13619/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1280769/10000000) (δ := 14457/1000000000) (ψ := -30537/500000) 289 229
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t145 : ((90469243533/1250000000000 : ℚ) : ℝ) ≤ stT289 145 := by
  have hc : ((217879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90469243533/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((217879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c146 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((19337/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3684901/10000000) (δ := 14557/1000000000) (ψ := -30537/500000) 289 229
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t146 : ((3197369157/400000000000 : ℚ) : ℝ) ≤ stT289 146 := by
  have hc : ((19317/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3197369157/400000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((19317/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c147 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-953831/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7091349/10000000) (δ := 14553/1000000000) (ψ := -30537/500000) 289 230
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t147 : ((-786789887697/10000000000000 : ℚ) : ℝ) ≤ stT289 147 := by
  have hc : ((-953931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-786789887697/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-953931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c148 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((319651/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -274127/1250000) (δ := 14453/1000000000) (ψ := -30537/500000) 289 230
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t148 : ((131355052197/2500000000000 : ℚ) : ℝ) ≤ stT289 148 := by
  have hc : ((319601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131355052197/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((319601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c149 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((240523/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2672371/10000000) (δ := 291/20000000) (ψ := -30537/500000) 289 230
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t149 : ((197002936263/5000000000000 : ℚ) : ℝ) ≤ stT289 149 := by
  have hc : ((240473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197002936263/5000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((240473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c150 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-495139/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7505101/10000000) (δ := 293/20000000) (ψ := -30537/500000) 289 230
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t150 : ((-404320332933/5000000000000 : ℚ) : ℝ) ≤ stT289 150 := by
  have hc : ((-495189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-404320332933/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-495189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c151 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((104201/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1701069/5000000) (δ := 91/6250000) (ψ := -30537/500000) 289 231
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t151 : ((21189208497/1250000000000 : ℚ) : ℝ) ≤ stT289 151 := by
  have hc : ((104151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21189208497/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((104151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c152 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((42711/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1366867/10000000) (δ := 14643/1000000000) (ψ := -30537/500000) 289 231
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t152 : ((17319567771/250000000000 : ℚ) : ℝ) ≤ stT289 152 := by
  have hc : ((21353/25000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17319567771/250000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((21353/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c153 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-764999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6104589/10000000) (δ := 723/50000000) (ψ := -30537/500000) 289 231
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t153 : ((-618546581847/10000000000000 : ℚ) : ℝ) ≤ stT289 153 := by
  have hc : ((-765099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-618546581847/10000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-765099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c154 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-189079/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -612063/1250000) (δ := 3659/250000000) (ψ := -30537/500000) 289 232
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t154 : ((-152404498167/5000000000000 : ℚ) : ℝ) ≤ stT289 154 := by
  have hc : ((-189129/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152404498167/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-189129/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c155 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((498063/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110061/5000000) (δ := 14567/1000000000) (ψ := -30537/500000) 289 232
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t155 : ((400013503847/5000000000000 : ℚ) : ℝ) ≤ stT289 155 := by
  have hc : ((498013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((400013503847/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((498013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c156 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-4959/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4426203/10000000) (δ := 14467/1000000000) (ψ := -30537/500000) 289 232
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t156 : ((-7944760643/500000000000 : ℚ) : ℝ) ≤ stT289 156 := by
  have hc : ((-9923/50000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7944760643/500000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-9923/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c157 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-177809/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -666513/1000000) (δ := 14529/1000000000) (ψ := -30537/500000) 289 233
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t157 : ((-141923013123/2000000000000 : ℚ) : ℝ) ≤ stT289 157 := by
  have hc : ((-177829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-141923013123/2000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-177829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c158 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((674039/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2077833/10000000) (δ := 14529/1000000000) (ψ := -30537/500000) 289 233
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t158 : ((536156889023/10000000000000 : ℚ) : ℝ) ≤ stT289 158 := by
  have hc : ((673939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((536156889023/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((673939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c159 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((136707/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 620141/2500000) (δ := 14529/1000000000) (ψ := -30537/500000) 289 233
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t159 : ((54197898391/1250000000000 : ℚ) : ℝ) ≤ stT289 159 := by
  have hc : ((68341/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54197898391/1250000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((68341/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c160 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-943601/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140207/200000) (δ := 14529/1000000000) (ψ := -30537/500000) 289 233
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t160 : ((-74606169957/1000000000000 : ℚ) : ℝ) ≤ stT289 160 := by
  have hc : ((-943701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74606169957/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-943701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c161 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-107427/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4196077/10000000) (δ := 14521/1000000000) (ψ := -30537/500000) 289 234
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t161 : ((-84743211497/10000000000000 : ℚ) : ℝ) ≤ stT289 161 := by
  have hc : ((-107527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84743211497/10000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-107527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c162 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((993839/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 277643/10000000) (δ := 14521/1000000000) (ψ := -30537/500000) 289 234
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t162 : ((390377447543/5000000000000 : ℚ) : ℝ) ≤ stT289 162 := by
  have hc : ((993739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((390377447543/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((993739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c163 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-39171/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1180959/2500000) (δ := 7241/500000000) (ψ := -30537/500000) 289 234
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t163 : ((-61381814787/2500000000000 : ℚ) : ℝ) ≤ stT289 163 := by
  have hc : ((-78367/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61381814787/2500000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-78367/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c164 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-174007/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6565173/10000000) (δ := 7257/500000000) (ψ := -30537/500000) 289 235
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t164 : ((-135892289463/2000000000000 : ℚ) : ℝ) ≤ stT289 164 := by
  have hc : ((-174027/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135892289463/2000000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-174027/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c165 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((645409/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -434619/2000000) (δ := 14589/1000000000) (ψ := -30537/500000) 289 235
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t165 : ((251185882941/5000000000000 : ℚ) : ℝ) ≤ stT289 165 := by
  have hc : ((645309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251185882941/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((645309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c166 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((639471/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1096233/5000000) (δ := 7307/500000000) (ψ := -30537/500000) 289 235
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t166 : ((9924956033/200000000000 : ℚ) : ℝ) ≤ stT289 166 := by
  have hc : ((639371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9924956033/200000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((639371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c167 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-863391/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3265937/5000000) (δ := 14589/1000000000) (ψ := -30537/500000) 289 235
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t167 : ((-10440469681/156250000000 : ℚ) : ℝ) ≤ stT289 167 := by
  have hc : ((-863491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10440469681/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-863491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c168 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-365603/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1215673/2500000) (δ := 3649/250000000) (ψ := -30537/500000) 289 236
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t168 : ((-282146081451/10000000000000 : ℚ) : ℝ) ≤ stT289 168 := by
  have hc : ((-365703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-282146081451/10000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-365703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c169 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((194737/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -574799/10000000) (δ := 3649/250000000) (ψ := -30537/500000) 289 236
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t169 : ((14978215791/200000000000 : ℚ) : ℝ) ≤ stT289 169 := by
  have hc : ((194717/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14978215791/200000000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((194717/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c170 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((95557/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1843867/5000000) (δ := 453/31250000) (ψ := -30537/500000) 289 236
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t170 : ((18303020637/2500000000000 : ℚ) : ℝ) ≤ stT289 170 := by
  have hc : ((95457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18303020637/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((95457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c171 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-999593/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1556539/2000000) (δ := 73/5000000) (ψ := -30537/500000) 289 237
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t171 : ((-9556065387/125000000000 : ℚ) : ℝ) ≤ stT289 171 := by
  have hc : ((-999693/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).2
  have h0 : (0:ℝ) ≤ ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9556065387/125000000000 : ℚ) : ℝ)
      = ((9559/125000 : ℚ) : ℝ) * ((-999693/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c172 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((142363/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3569869/10000000) (δ := 14603/1000000000) (ψ := -30537/500000) 289 237
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t172 : ((27118599849/2500000000000 : ℚ) : ℝ) ≤ stT289 172 := by
  have hc : ((142263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27118599849/2500000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((142263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c173 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((969549/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 123707/2000000) (δ := 73/5000000) (ψ := -30537/500000) 289 237
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t173 : ((147411506593/2000000000000 : ℚ) : ℝ) ≤ stT289 173 := by
  have hc : ((969449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((147411506593/2000000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((969449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c174 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-1049/3125 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4782809/10000000) (δ := 14603/1000000000) (ψ := -30537/500000) 289 237
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t174 : ((-12727724111/500000000000 : ℚ) : ℝ) ≤ stT289 174 := by
  have hc : ((-16789/50000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12727724111/500000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-16789/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c175 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-909921/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1696181/2500000) (δ := 14493/1000000000) (ψ := -30537/500000) 289 238
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t175 : ((-687911264509/10000000000000 : ℚ) : ℝ) ≤ stT289 175 := by
  have hc : ((-910021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-687911264509/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-910021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c176 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((482607/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2667919/10000000) (δ := 14493/1000000000) (ψ := -30537/500000) 289 238
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t176 : ((181851580723/5000000000000 : ℚ) : ℝ) ≤ stT289 176 := by
  have hc : ((482507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181851580723/5000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((482507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c177 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((841767/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 712811/5000000) (δ := 1461/100000000) (ψ := -30537/500000) 289 238
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t177 : ((316317816941/5000000000000 : ℚ) : ℝ) ≤ stT289 177 := by
  have hc : ((841667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((316317816941/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((841667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c178 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-29361/50000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2748021/5000000) (δ := 14493/1000000000) (ψ := -30537/500000) 289 238
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t178 : ((-2751344589/62500000000 : ℚ) : ℝ) ≤ stT289 178 := by
  have hc : ((-14683/25000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2751344589/62500000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-14683/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c179 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-780151/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6164259/10000000) (δ := 14617/1000000000) (ψ := -30537/500000) 289 239
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t179 : ((-145796921609/2500000000000 : ℚ) : ℝ) ≤ stT289 179 := by
  have hc : ((-780251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145796921609/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-780251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c180 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((327851/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -534803/2500000) (δ := 7243/500000000) (ψ := -30537/500000) 289 239
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t180 : ((48865622871/1000000000000 : ℚ) : ℝ) ≤ stT289 180 := by
  have hc : ((327801/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48865622871/1000000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((327801/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c181 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((367397/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1863583/10000000) (δ := 14617/1000000000) (ψ := -30537/500000) 289 239
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t181 : ((136523410509/2500000000000 : ℚ) : ℝ) ≤ stT289 181 := by
  have hc : ((367347/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136523410509/2500000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((367347/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c182 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-346957/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5844269/10000000) (δ := 14617/1000000000) (ψ := -30537/500000) 289 239
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t182 : ((-205775151/4000000000 : ℚ) : ℝ) ≤ stT289 182 := by
  have hc : ((-347007/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205775151/4000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-347007/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c183 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-711131/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1476189/2500000) (δ := 7239/500000000) (ψ := -30537/500000) 289 240
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t183 : ((-262878801141/5000000000000 : ℚ) : ℝ) ≤ stT289 183 := by
  have hc : ((-711231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-262878801141/5000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-711231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c184 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((176499/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98371/500000) (δ := 7239/500000000) (ψ := -30537/500000) 289 240
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t184 : ((65049110533/1250000000000 : ℚ) : ℝ) ≤ stT289 184 := by
  have hc : ((88237/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65049110533/1250000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((88237/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c185 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((711307/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 974301/5000000) (δ := 7289/500000000) (ψ := -30537/500000) 289 240
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t185 : ((261444671649/5000000000000 : ℚ) : ℝ) ≤ stT289 185 := by
  have hc : ((711207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((261444671649/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((711207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c186 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-8671/12500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1168691/2000000) (δ := 7289/500000000) (ψ := -30537/500000) 289 240
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t186 : ((-6358805901/125000000000 : ℚ) : ℝ) ≤ stT289 186 := by
  have hc : ((-34689/50000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6358805901/125000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-34689/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c187 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-183703/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5990463/10000000) (δ := 14471/1000000000) (ψ := -30537/500000) 289 241
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t187 : ((-8397207859/156250000000 : ℚ) : ℝ) ≤ stT289 187 := by
  have hc : ((-11483/15625 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8397207859/156250000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-11483/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c188 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((656323/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1068577/5000000) (δ := 14571/1000000000) (ψ := -30537/500000) 289 241
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t188 : ((119649795813/2500000000000 : ℚ) : ℝ) ≤ stT289 188 := by
  have hc : ((656223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).1
  have hw2 : ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((182331/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119649795813/2500000000000 : ℚ) : ℝ)
      = ((182331/2500000 : ℚ) : ℝ) * ((656223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c189 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((778633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1695781/10000000) (δ := 14471/1000000000) (ψ := -30537/500000) 289 241
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t189 : ((17696833623/312500000000 : ℚ) : ℝ) ≤ stT289 189 := by
  have hc : ((778533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17696833623/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((778533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c190 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-591219/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2754207/5000000) (δ := 1829/125000000) (ψ := -30537/500000) 289 241
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t190 : ((-428988334163/10000000000000 : ℚ) : ℝ) ≤ stT289 190 := by
  have hc : ((-591319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-428988334163/10000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-591319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c191 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-837093/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3203429/5000000) (δ := 14539/1000000000) (ψ := -30537/500000) 289 242
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t191 : ((-24230876999/400000000000 : ℚ) : ℝ) ≤ stT289 191 := by
  have hc : ((-837193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24230876999/400000000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-837193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c192 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((494433/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -526807/2000000) (δ := 14639/1000000000) (ψ := -30537/500000) 289 242
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t192 : ((356753699771/10000000000000 : ℚ) : ℝ) ≤ stT289 192 := by
  have hc : ((494333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((356753699771/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((494333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c193 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((225363/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 139901/1250000) (δ := 14639/1000000000) (ψ := -30537/500000) 289 242
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t193 : ((16220167247/250000000000 : ℚ) : ℝ) ≤ stT289 193 := by
  have hc : ((112669/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16220167247/250000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((112669/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c194 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-14481/40000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 151659/312500) (δ := 14639/1000000000) (ψ := -30537/500000) 289 242
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t194 : ((-2079927223/80000000000 : ℚ) : ℝ) ≤ stT289 194 := by
  have hc : ((-2897/8000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2079927223/80000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-2897/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c195 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-959519/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3570107/5000000) (δ := 7273/500000000) (ψ := -30537/500000) 289 243
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t195 : ((-137439512037/2000000000000 : ℚ) : ℝ) ≤ stT289 195 := by
  have hc : ((-959619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137439512037/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-959619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c196 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((191779/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1722277/5000000) (δ := 7323/500000000) (ψ := -30537/500000) 289 243
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t196 : ((27382686903/2000000000000 : ℚ) : ℝ) ≤ stT289 196 := by
  have hc : ((191679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27382686903/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((191679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c197 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((199137/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363/15625) (δ := 14557/1000000000) (ψ := -30537/500000) 289 243
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t197 : ((14186488899/200000000000 : ℚ) : ℝ) ≤ stT289 197 := by
  have hc : ((199117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14186488899/200000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((199117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c198 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((7287/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 778111/2000000) (δ := 7323/500000000) (ψ := -30537/500000) 289 243
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t198 : ((5143111553/5000000000000 : ℚ) : ℝ) ≤ stT289 198 := by
  have hc : ((7237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5143111553/5000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((7237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c199 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-991633/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1506073/2000000) (δ := 14457/1000000000) (ψ := -30537/500000) 289 243
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t199 : ((-351510836253/5000000000000 : ℚ) : ℝ) ≤ stT289 199 := by
  have hc : ((-991733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-351510836253/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-991733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c200 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-248983/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4556067/10000000) (δ := 14453/1000000000) (ψ := -30537/500000) 289 244
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t200 : ((-176128332881/10000000000000 : ℚ) : ℝ) ≤ stT289 200 := by
  have hc : ((-249083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176128332881/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-249083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c201 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((928289/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -476263/5000000) (δ := 14453/1000000000) (ψ := -30537/500000) 289 244
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t201 : ((130938694041/2000000000000 : ℚ) : ℝ) ≤ stT289 201 := by
  have hc : ((928189/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130938694041/2000000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((928189/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c202 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((7731/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 105321/400000) (δ := 14553/1000000000) (ψ := -30537/500000) 289 244
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t202 : ((87014544587/2500000000000 : ℚ) : ℝ) ≤ stT289 202 := by
  have hc : ((123671/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87014544587/2500000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((123671/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c203 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-789247/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3100473/5000000) (δ := 293/20000000) (ψ := -30537/500000) 289 244
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t203 : ((-554013453461/10000000000000 : ℚ) : ℝ) ≤ stT289 203 := by
  have hc : ((-789347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-554013453461/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-789347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c204 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-725571/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1489163/2500000) (δ := 14543/1000000000) (ψ := -30537/500000) 289 245
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t204 : ((-508072019611/10000000000000 : ℚ) : ℝ) ≤ stT289 204 := by
  have hc : ((-725671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-508072019611/10000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-725671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c205 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((70719/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2423627/10000000) (δ := 14543/1000000000) (ψ := -30537/500000) 289 245
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t205 : ((9876708159/250000000000 : ℚ) : ℝ) ≤ stT289 205 := by
  have hc : ((141413/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9876708159/250000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((141413/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c206 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((226519/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1092203/10000000) (δ := 91/6250000) (ψ := -30537/500000) 289 245
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t206 : ((78902922051/1250000000000 : ℚ) : ℝ) ≤ stT289 206 := by
  have hc : ((113247/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78902922051/1250000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((113247/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c207 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-65621/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4590981/10000000) (δ := 14543/1000000000) (ψ := -30537/500000) 289 245
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t207 : ((-22813593327/1250000000000 : ℚ) : ℝ) ≤ stT289 207 := by
  have hc : ((-32823/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22813593327/1250000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-32823/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c208 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-124521/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3817519/5000000) (δ := 2907/200000000) (ψ := -30537/500000) 289 246
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t208 : ((-1349195939/19531250000 : ℚ) : ℝ) ≤ stT289 208 := by
  have hc : ((-249067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1349195939/19531250000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-249067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c209 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-24241/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4169783/10000000) (δ := 1821/125000000) (ψ := -30537/500000) 289 246
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t209 : ((-1678515619/250000000000 : ℚ) : ℝ) ≤ stT289 209 := by
  have hc : ((-12133/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1678515619/250000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-12133/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c210 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((239673/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -360537/5000000) (δ := 3617/250000000) (ψ := -30537/500000) 289 246
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t210 : ((1033579357/15625000000 : ℚ) : ℝ) ≤ stT289 210 := by
  have hc : ((14978/15625 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1033579357/15625000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((14978/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c211 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((2921/6250 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1355617/5000000) (δ := 2927/200000000) (ψ := -30537/500000) 289 246
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t211 : ((4020935841/125000000000 : ℚ) : ℝ) ≤ stT289 211 := by
  have hc : ((23363/50000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4020935841/125000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((23363/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c212 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-385407/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6127287/10000000) (δ := 1821/125000000) (ψ := -30537/500000) 289 246
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t212 : ((-264733023971/5000000000000 : ℚ) : ℝ) ≤ stT289 212 := by
  have hc : ((-385457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264733023971/5000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-385457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c213 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-784239/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -772583/1250000) (δ := 227/15625000) (ψ := -30537/500000) 289 247
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t213 : ((-537420455071/10000000000000 : ℚ) : ℝ) ≤ stT289 213 := by
  have hc : ((-784339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-537420455071/10000000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-784339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c214 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((218463/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1398273/5000000) (δ := 579/40000000) (ψ := -30537/500000) 289 247
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t214 : ((29860770121/1000000000000 : ℚ) : ℝ) ≤ stT289 214 := by
  have hc : ((218413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29860770121/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((218413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c215 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((486981/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 571749/10000000) (δ := 579/40000000) (ψ := -30537/500000) 289 247
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t215 : ((166042010207/2500000000000 : ℚ) : ℝ) ≤ stT289 215 := by
  have hc : ((486931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).1
  have hw2 : ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((340997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166042010207/2500000000000 : ℚ) : ℝ)
      = ((340997/5000000 : ℚ) : ℝ) * ((486931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c216 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((1021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1962219/5000000) (δ := 579/40000000) (ψ := -30537/500000) 289 247
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t216 : ((626660373/10000000000000 : ℚ) : ℝ) ≤ stT289 216 := by
  have hc : ((921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((626660373/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c217 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-972057/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7261593/10000000) (δ := 227/15625000) (ψ := -30537/500000) 289 247
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t217 : ((-131988783733/2000000000000 : ℚ) : ℝ) ≤ stT289 217 := by
  have hc : ((-972157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131988783733/2000000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-972157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c218 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-460907/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1281133/2500000) (δ := 14521/1000000000) (ψ := -30537/500000) 289 248
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t218 : ((-156116793501/5000000000000 : ℚ) : ℝ) ≤ stT289 218 := by
  have hc : ((-461007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).2
  have h0 : (0:ℝ) ≤ ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156116793501/5000000000000 : ℚ) : ℝ)
      = ((338643/5000000 : ℚ) : ℝ) * ((-461007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c219 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((373537/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -908933/5000000) (δ := 7241/500000000) (ψ := -30537/500000) 289 248
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t219 : ((252378984919/5000000000000 : ℚ) : ℝ) ≤ stT289 219 := by
  have hc : ((373487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252378984919/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((373487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c220 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((83123/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473699/10000000) (δ := 14621/1000000000) (ψ := -30537/500000) 289 248
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t220 : ((56034701487/1000000000000 : ℚ) : ℝ) ≤ stT289 220 := by
  have hc : ((83113/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56034701487/1000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((83113/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c221 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-161717/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4750381/10000000) (δ := 14621/1000000000) (ψ := -30537/500000) 289 248
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t221 : ((-108816293191/5000000000000 : ℚ) : ℝ) ≤ stT289 221 := by
  have hc : ((-161767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108816293191/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-161767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c222 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-997999/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7695783/10000000) (δ := 14589/1000000000) (ψ := -30537/500000) 289 249
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t222 : ((-669881130543/10000000000000 : ℚ) : ℝ) ≤ stT289 222 := by
  have hc : ((-998099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-669881130543/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-998099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c223 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-1657/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4448579/10000000) (δ := 14589/1000000000) (ψ := -30537/500000) 289 249
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t223 : ((-111014577/8000000000 : ℚ) : ℝ) ≤ stT289 223 := by
  have hc : ((-8289/40000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111014577/8000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-8289/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c224 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((22101/25000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -607949/5000000) (δ := 7307/500000000) (ψ := -30537/500000) 289 249
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t224 : ((29530358141/500000000000 : ℚ) : ℝ) ≤ stT289 224 := by
  have hc : ((44197/50000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29530358141/500000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((44197/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c225 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((43501/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1001203/5000000) (δ := 7307/500000000) (ψ := -30537/500000) 289 249
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t225 : ((57992942007/1250000000000 : ℚ) : ℝ) ≤ stT289 225 := by
  have hc : ((173979/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57992942007/1250000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((173979/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c226 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-97941/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5206369/10000000) (δ := 28989/1000000000) (ψ := -30537/500000) 289 249
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t226 : ((-65162775551/2000000000000 : ℚ) : ℝ) ≤ stT289 226 := by
  have hc : ((-97961/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).2
  have h0 : (0:ℝ) ≤ ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65162775551/2000000000000 : ℚ) : ℝ)
      = ((665191/10000000 : ℚ) : ℝ) * ((-97961/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c227 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-122071/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7311721/10000000) (δ := 14507/1000000000) (ψ := -30537/500000) 289 250
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t227 : ((-40514874477/625000000000 : ℚ) : ℝ) ≤ stT289 227 := by
  have hc : ((-244167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).2
  have h0 : (0:ℝ) ≤ ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40514874477/625000000000 : ℚ) : ℝ)
      = ((165931/2500000 : ℚ) : ℝ) * ((-244167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c228 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-41733/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41359/100000) (δ := 14507/1000000000) (ψ := -30537/500000) 289 250
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t228 : ((-27671502061/5000000000000 : ℚ) : ℝ) ≤ stT289 228 := by
  have hc : ((-41783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27671502061/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-41783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c229 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((925069/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -973951/10000000) (δ := 14507/1000000000) (ψ := -30537/500000) 289 250
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t229 : ((305618082321/5000000000000 : ℚ) : ℝ) ≤ stT289 229 := by
  have hc : ((924969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305618082321/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((924969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c230 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((40317/62500 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1087099/5000000) (δ := 14607/1000000000) (ψ := -30537/500000) 289 250
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t230 : ((5316020467/125000000000 : ℚ) : ℝ) ≤ stT289 230 := by
  have hc : ((161243/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).1
  have hw2 : ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((32969/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5316020467/125000000000 : ℚ) : ℝ)
      = ((32969/500000 : ℚ) : ℝ) * ((161243/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c231 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-524971/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1327173/2500000) (δ := 14607/1000000000) (ψ := -30537/500000) 289 250
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t231 : ((-10795984831/312500000000 : ℚ) : ℝ) ≤ stT289 231 := by
  have hc : ((-525071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10795984831/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-525071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c232 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-97361/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -181959/250000) (δ := 14499/1000000000) (ψ := -30537/500000) 289 251
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t232 : ((-63927274743/1000000000000 : ℚ) : ℝ) ≤ stT289 232 := by
  have hc : ((-97371/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-63927274743/1000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-97371/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c233 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-779/8000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -834163/2000000) (δ := 1813/125000000) (ψ := -30537/500000) 289 251
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t233 : ((-1277160339/200000000000 : ℚ) : ℝ) ≤ stT289 233 := by
  have hc : ((-3899/40000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1277160339/200000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-3899/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c234 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((181741/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269141/2500000) (δ := 3651/250000000) (ψ := -30537/500000) 289 251
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t234 : ((2969866303/50000000000 : ℚ) : ℝ) ≤ stT289 234 := by
  have hc : ((181721/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2969866303/50000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((181721/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c235 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((10866/15625 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 400893/2000000) (δ := 3651/250000000) (ψ := -30537/500000) 289 251
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t235 : ((14174353571/312500000000 : ℚ) : ℝ) ≤ stT289 235 := by
  have hc : ((173831/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14174353571/312500000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((173831/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c236 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-110577/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 158513/312500) (δ := 14599/1000000000) (ψ := -30537/500000) 289 251
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t236 : ((-7199581889/250000000000 : ℚ) : ℝ) ≤ stT289 236 := by
  have hc : ((-55301/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7199581889/250000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-55301/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c237 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-994027/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37903/50000) (δ := 14511/1000000000) (ψ := -30537/500000) 289 252
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t237 : ((-64575507539/1000000000000 : ℚ) : ℝ) ≤ stT289 237 := by
  have hc : ((-994127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).2
  have h0 : (0:ℝ) ≤ ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64575507539/1000000000000 : ℚ) : ℝ)
      = ((64957/1000000 : ℚ) : ℝ) * ((-994127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c238 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-242177/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2269257/5000000) (δ := 3623/250000000) (ψ := -30537/500000) 289 252
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t238 : ((-39261230127/2500000000000 : ℚ) : ℝ) ≤ stT289 238 := by
  have hc : ((-242277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39261230127/2500000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-242277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c239 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((164653/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188643/1250000) (δ := 57/3906250) (ψ := -30537/500000) 289 252
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t239 : ((53246098759/1000000000000 : ℚ) : ℝ) ≤ stT289 239 := by
  have hc : ((164633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((53246098759/1000000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((164633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c240 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((823619/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1507583/10000000) (δ := 14511/1000000000) (ψ := -30537/500000) 289 252
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t240 : ((531579043943/10000000000000 : ℚ) : ℝ) ≤ stT289 240 := by
  have hc : ((823519/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((531579043943/10000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((823519/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c241 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-57943/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2255869/5000000) (δ := 14511/1000000000) (ψ := -30537/500000) 289 252
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t241 : ((-2333780811/156250000000 : ℚ) : ℝ) ≤ stT289 241 := by
  have hc : ((-3623/15625 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2333780811/156250000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-3623/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c242 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-990187/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3751733/5000000) (δ := 14511/1000000000) (ψ := -30537/500000) 289 252
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t242 : ((-25463249631/400000000000 : ℚ) : ℝ) ≤ stT289 242 := by
  have hc : ((-990287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25463249631/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-990287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c243 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-62029/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1306281/2500000) (δ := 7259/500000000) (ψ := -30537/500000) 289 253
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t243 : ((-79599368583/2500000000000 : ℚ) : ℝ) ≤ stT289 243 := by
  have hc : ((-124083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79599368583/2500000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-124083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c244 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((77389/125000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2257961/10000000) (δ := 7259/500000000) (ψ := -30537/500000) 289 253
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t244 : ((12383799319/312500000000 : ℚ) : ℝ) ≤ stT289 244 := by
  have hc : ((154753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12383799319/312500000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((154753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c245 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((961383/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174257/2500000) (δ := 14509/500000000) (ψ := -30537/500000) 289 253
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t245 : ((153535159477/2500000000000 : ℚ) : ℝ) ≤ stT289 245 := by
  have hc : ((961283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153535159477/2500000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((961283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c246 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((22907/200000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3640023/10000000) (δ := 2897/200000000) (ψ := -30537/500000) 289 253
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t246 : ((1824025239/250000000000 : ℚ) : ℝ) ≤ stT289 246 := by
  have hc : ((22887/200000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1824025239/250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((22887/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c247 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-871193/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6571061/10000000) (δ := 2897/200000000) (ψ := -30537/500000) 289 253
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t247 : ((-110878133301/2000000000000 : ℚ) : ℝ) ≤ stT289 247 := by
  have hc : ((-871293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110878133301/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-871293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c248 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-198337/250000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6217713/10000000) (δ := 581/40000000) (ψ := -30537/500000) 289 254
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t248 : ((-62980034181/1250000000000 : ℚ) : ℝ) ≤ stT289 248 := by
  have hc : ((-99181/125000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62980034181/1250000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-99181/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c249 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((122091/500000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3310301/10000000) (δ := 7239/500000000) (ψ := -30537/500000) 289 254
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t249 : ((19335077671/1250000000000 : ℚ) : ℝ) ≤ stT289 249 := by
  have hc : ((122041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).1
  have hw2 : ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((158431/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19335077671/1250000000000 : ℚ) : ℝ)
      = ((158431/2500000 : ℚ) : ℝ) * ((122041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_c250 :
    |Real.cos (((289 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((98629/100000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414449/10000000) (δ := 7289/500000000) (ψ := -30537/500000) 289 254
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st289_t250 : ((12474415929/200000000000 : ℚ) : ℝ) ≤ stT289 250 := by
  have hc : ((98619/100000 : ℚ) : ℝ)
      ≤ Real.cos (((289 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st289_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).1
  have hw2 : ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126491/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12474415929/200000000000 : ℚ) : ℝ)
      = ((126491/2000000 : ℚ) : ℝ) * ((98619/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st289_p1 : ((249509/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT289 (i+1) := by
  rw [Finset.sum_range_one]
  exact st289_t1

theorem st289_p2 : ((3868001297653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT289 (i+1))
      = (∑ i ∈ Finset.range 1, stT289 (i+1)) + stT289 2 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 1
    simpa using h
  have hprev := st289_p1
  have hstep := st289_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p3 : ((9890719425991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT289 (i+1))
      = (∑ i ∈ Finset.range 2, stT289 (i+1)) + stT289 3 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 2
    simpa using h
  have hprev := st289_p2
  have hstep := st289_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p4 : ((10622959425991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT289 (i+1))
      = (∑ i ∈ Finset.range 3, stT289 (i+1)) + stT289 4 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 3
    simpa using h
  have hprev := st289_p3
  have hstep := st289_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p5 : ((467933662713/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT289 (i+1))
      = (∑ i ∈ Finset.range 4, stT289 (i+1)) + stT289 5 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 4
    simpa using h
  have hprev := st289_p4
  have hstep := st289_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p6 : ((5679219213491/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT289 (i+1))
      = (∑ i ∈ Finset.range 5, stT289 (i+1)) + stT289 6 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 5
    simpa using h
  have hprev := st289_p5
  have hstep := st289_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p7 : ((3795875025021/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT289 (i+1))
      = (∑ i ∈ Finset.range 6, stT289 (i+1)) + stT289 7 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 6
    simpa using h
  have hprev := st289_p6
  have hstep := st289_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p8 : ((350549106379/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT289 (i+1))
      = (∑ i ∈ Finset.range 7, stT289 (i+1)) + stT289 8 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 7
    simpa using h
  have hprev := st289_p7
  have hstep := st289_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p9 : ((8599348736341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT289 (i+1))
      = (∑ i ∈ Finset.range 8, stT289 (i+1)) + stT289 9 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 8
    simpa using h
  have hprev := st289_p8
  have hstep := st289_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p10 : ((11359681355979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT289 (i+1))
      = (∑ i ∈ Finset.range 9, stT289 (i+1)) + stT289 10 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 9
    simpa using h
  have hprev := st289_p9
  have hstep := st289_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p11 : ((2075546217783/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT289 (i+1))
      = (∑ i ∈ Finset.range 10, stT289 (i+1)) + stT289 11 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 10
    simpa using h
  have hprev := st289_p10
  have hstep := st289_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p12 : ((9400678120243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT289 (i+1))
      = (∑ i ∈ Finset.range 11, stT289 (i+1)) + stT289 12 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 11
    simpa using h
  have hprev := st289_p11
  have hstep := st289_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p13 : ((12164021563243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT289 (i+1))
      = (∑ i ∈ Finset.range 12, stT289 (i+1)) + stT289 13 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 12
    simpa using h
  have hprev := st289_p12
  have hstep := st289_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p14 : ((5024868063617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT289 (i+1))
      = (∑ i ∈ Finset.range 13, stT289 (i+1)) + stT289 14 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 13
    simpa using h
  have hprev := st289_p13
  have hstep := st289_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p15 : ((1925910701563/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT289 (i+1))
      = (∑ i ∈ Finset.range 14, stT289 (i+1)) + stT289 15 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 14
    simpa using h
  have hprev := st289_p14
  have hstep := st289_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p16 : ((1317750458299/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT289 (i+1))
      = (∑ i ∈ Finset.range 15, stT289 (i+1)) + stT289 16 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 15
    simpa using h
  have hprev := st289_p15
  have hstep := st289_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p17 : ((2080940613191/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT289 (i+1))
      = (∑ i ∈ Finset.range 16, stT289 (i+1)) + stT289 17 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 16
    simpa using h
  have hprev := st289_p16
  have hstep := st289_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p18 : ((802937255861/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT289 (i+1))
      = (∑ i ∈ Finset.range 17, stT289 (i+1)) + stT289 18 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 17
    simpa using h
  have hprev := st289_p17
  have hstep := st289_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p19 : ((535305371897/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT289 (i+1))
      = (∑ i ∈ Finset.range 18, stT289 (i+1)) + stT289 19 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 18
    simpa using h
  have hprev := st289_p18
  have hstep := st289_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p20 : ((622914476957/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT289 (i+1))
      = (∑ i ∈ Finset.range 19, stT289 (i+1)) + stT289 20 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 19
    simpa using h
  have hprev := st289_p19
  have hstep := st289_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p21 : ((176975243429/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT289 (i+1))
      = (∑ i ∈ Finset.range 20, stT289 (i+1)) + stT289 21 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 20
    simpa using h
  have hprev := st289_p20
  have hstep := st289_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p22 : ((7930134647651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT289 (i+1))
      = (∑ i ∈ Finset.range 21, stT289 (i+1)) + stT289 22 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 21
    simpa using h
  have hprev := st289_p21
  have hstep := st289_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p23 : ((8201407711763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT289 (i+1))
      = (∑ i ∈ Finset.range 22, stT289 (i+1)) + stT289 23 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 22
    simpa using h
  have hprev := st289_p22
  have hstep := st289_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p24 : ((4495429854877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT289 (i+1))
      = (∑ i ∈ Finset.range 23, stT289 (i+1)) + stT289 24 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 23
    simpa using h
  have hprev := st289_p23
  have hstep := st289_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p25 : ((5414522854877/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT289 (i+1))
      = (∑ i ∈ Finset.range 24, stT289 (i+1)) + stT289 25 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 24
    simpa using h
  have hprev := st289_p24
  have hstep := st289_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p26 : ((6078493523037/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT289 (i+1))
      = (∑ i ∈ Finset.range 25, stT289 (i+1)) + stT289 26 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 25
    simpa using h
  have hprev := st289_p25
  have hstep := st289_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p27 : ((10630982845639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT289 (i+1))
      = (∑ i ∈ Finset.range 26, stT289 (i+1)) + stT289 27 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 26
    simpa using h
  have hprev := st289_p26
  have hstep := st289_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p28 : ((10310994235633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT289 (i+1))
      = (∑ i ∈ Finset.range 27, stT289 (i+1)) + stT289 28 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 27
    simpa using h
  have hprev := st289_p27
  have hstep := st289_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p29 : ((11749869123307/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT289 (i+1))
      = (∑ i ∈ Finset.range 28, stT289 (i+1)) + stT289 29 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 28
    simpa using h
  have hprev := st289_p28
  have hstep := st289_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p30 : ((10011748133371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT289 (i+1))
      = (∑ i ∈ Finset.range 29, stT289 (i+1)) + stT289 30 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 29
    simpa using h
  have hprev := st289_p29
  have hstep := st289_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p31 : ((469892259049/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT289 (i+1))
      = (∑ i ∈ Finset.range 30, stT289 (i+1)) + stT289 31 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 30
    simpa using h
  have hprev := st289_p30
  have hstep := st289_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p32 : ((5101855888631/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT289 (i+1))
      = (∑ i ∈ Finset.range 31, stT289 (i+1)) + stT289 32 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 31
    simpa using h
  have hprev := st289_p31
  have hstep := st289_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p33 : ((5541567202351/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT289 (i+1))
      = (∑ i ∈ Finset.range 32, stT289 (i+1)) + stT289 33 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 32
    simpa using h
  have hprev := st289_p32
  have hstep := st289_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p34 : ((11536341485757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT289 (i+1))
      = (∑ i ∈ Finset.range 33, stT289 (i+1)) + stT289 34 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 33
    simpa using h
  have hprev := st289_p33
  have hstep := st289_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p35 : ((309402858261/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT289 (i+1))
      = (∑ i ∈ Finset.range 34, stT289 (i+1)) + stT289 35 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 34
    simpa using h
  have hprev := st289_p34
  have hstep := st289_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p36 : ((5381144726563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT289 (i+1))
      = (∑ i ∈ Finset.range 35, stT289 (i+1)) + stT289 36 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 35
    simpa using h
  have hprev := st289_p35
  have hstep := st289_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p37 : ((6055936451503/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT289 (i+1))
      = (∑ i ∈ Finset.range 36, stT289 (i+1)) + stT289 37 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 36
    simpa using h
  have hprev := st289_p36
  have hstep := st289_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p38 : ((11390472270291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT289 (i+1))
      = (∑ i ∈ Finset.range 37, stT289 (i+1)) + stT289 38 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 37
    simpa using h
  have hprev := st289_p37
  have hstep := st289_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p39 : ((9799363214837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT289 (i+1))
      = (∑ i ∈ Finset.range 38, stT289 (i+1)) + stT289 39 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 38
    simpa using h
  have hprev := st289_p38
  have hstep := st289_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p40 : ((2287368098771/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT289 (i+1))
      = (∑ i ∈ Finset.range 39, stT289 (i+1)) + stT289 40 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 39
    simpa using h
  have hprev := st289_p39
  have hstep := st289_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p41 : ((9799656304661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT289 (i+1))
      = (∑ i ∈ Finset.range 40, stT289 (i+1)) + stT289 41 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 40
    simpa using h
  have hprev := st289_p40
  have hstep := st289_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p42 : ((223639123723/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT289 (i+1))
      = (∑ i ∈ Finset.range 41, stT289 (i+1)) + stT289 42 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 41
    simpa using h
  have hprev := st289_p41
  have hstep := st289_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p43 : ((1270432431189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT289 (i+1))
      = (∑ i ∈ Finset.range 42, stT289 (i+1)) + stT289 43 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 42
    simpa using h
  have hprev := st289_p42
  have hstep := st289_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p44 : ((7041076805267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT289 (i+1))
      = (∑ i ∈ Finset.range 43, stT289 (i+1)) + stT289 44 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 43
    simpa using h
  have hprev := st289_p43
  have hstep := st289_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p45 : ((3057467063261/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT289 (i+1))
      = (∑ i ∈ Finset.range 44, stT289 (i+1)) + stT289 45 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 44
    simpa using h
  have hprev := st289_p44
  have hstep := st289_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p46 : ((8208481453787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT289 (i+1))
      = (∑ i ∈ Finset.range 45, stT289 (i+1)) + stT289 46 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 45
    simpa using h
  have hprev := st289_p45
  have hstep := st289_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p47 : ((8797746476807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT289 (i+1))
      = (∑ i ∈ Finset.range 46, stT289 (i+1)) + stT289 47 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 46
    simpa using h
  have hprev := st289_p46
  have hstep := st289_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p48 : ((9453304307807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT289 (i+1))
      = (∑ i ∈ Finset.range 47, stT289 (i+1)) + stT289 48 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 47
    simpa using h
  have hprev := st289_p47
  have hstep := st289_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p49 : ((1016343695191/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT289 (i+1))
      = (∑ i ∈ Finset.range 48, stT289 (i+1)) + stT289 49 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 48
    simpa using h
  have hprev := st289_p48
  have hstep := st289_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p50 : ((10830553750909/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT289 (i+1))
      = (∑ i ∈ Finset.range 49, stT289 (i+1)) + stT289 50 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 49
    simpa using h
  have hprev := st289_p49
  have hstep := st289_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p51 : ((11266873997509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT289 (i+1))
      = (∑ i ∈ Finset.range 50, stT289 (i+1)) + stT289 51 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 50
    simpa using h
  have hprev := st289_p50
  have hstep := st289_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p52 : ((11267905739509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT289 (i+1))
      = (∑ i ∈ Finset.range 51, stT289 (i+1)) + stT289 52 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 51
    simpa using h
  have hprev := st289_p51
  have hstep := st289_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p53 : ((10786452715691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT289 (i+1))
      = (∑ i ∈ Finset.range 52, stT289 (i+1)) + stT289 53 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 52
    simpa using h
  have hprev := st289_p52
  have hstep := st289_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p54 : ((2021709344339/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT289 (i+1))
      = (∑ i ∈ Finset.range 53, stT289 (i+1)) + stT289 54 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 53
    simpa using h
  have hprev := st289_p53
  have hstep := st289_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p55 : ((1956640819099/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT289 (i+1))
      = (∑ i ∈ Finset.range 54, stT289 (i+1)) + stT289 55 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 54
    simpa using h
  have hprev := st289_p54
  have hstep := st289_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p56 : ((10145030325891/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT289 (i+1))
      = (∑ i ∈ Finset.range 55, stT289 (i+1)) + stT289 56 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 55
    simpa using h
  have hprev := st289_p55
  have hstep := st289_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p57 : ((10797729893521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT289 (i+1))
      = (∑ i ∈ Finset.range 56, stT289 (i+1)) + stT289 57 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 56
    simpa using h
  have hprev := st289_p56
  have hstep := st289_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p58 : ((10892047280641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT289 (i+1))
      = (∑ i ∈ Finset.range 57, stT289 (i+1)) + stT289 58 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 57
    simpa using h
  have hprev := st289_p57
  have hstep := st289_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p59 : ((5142798162113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT289 (i+1))
      = (∑ i ∈ Finset.range 58, stT289 (i+1)) + stT289 59 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 58
    simpa using h
  have hprev := st289_p58
  have hstep := st289_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p60 : ((19932941503387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT289 (i+1))
      = (∑ i ∈ Finset.range 59, stT289 (i+1)) + stT289 60 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 59
    simpa using h
  have hprev := st289_p59
  have hstep := st289_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p61 : ((21002673602971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT289 (i+1))
      = (∑ i ∈ Finset.range 60, stT289 (i+1)) + stT289 61 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 60
    simpa using h
  have hprev := st289_p60
  have hstep := st289_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p62 : ((2168626307123/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT289 (i+1))
      = (∑ i ∈ Finset.range 61, stT289 (i+1)) + stT289 62 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 61
    simpa using h
  have hprev := st289_p61
  have hstep := st289_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p63 : ((128554712729/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT289 (i+1))
      = (∑ i ∈ Finset.range 62, stT289 (i+1)) + stT289 63 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 62
    simpa using h
  have hprev := st289_p62
  have hstep := st289_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p64 : ((10088253111421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT289 (i+1))
      = (∑ i ∈ Finset.range 63, stT289 (i+1)) + stT289 64 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 63
    simpa using h
  have hprev := st289_p63
  have hstep := st289_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p65 : ((167281199557/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT289 (i+1))
      = (∑ i ∈ Finset.range 64, stT289 (i+1)) + stT289 65 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 64
    simpa using h
  have hprev := st289_p64
  have hstep := st289_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p66 : ((5288014690229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT289 (i+1))
      = (∑ i ∈ Finset.range 65, stT289 (i+1)) + stT289 66 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 65
    simpa using h
  have hprev := st289_p65
  have hstep := st289_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p67 : ((1258089782361/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT289 (i+1))
      = (∑ i ∈ Finset.range 66, stT289 (i+1)) + stT289 67 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 66
    simpa using h
  have hprev := st289_p66
  have hstep := st289_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p68 : ((41320715097/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT289 (i+1))
      = (∑ i ∈ Finset.range 67, stT289 (i+1)) + stT289 68 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 67
    simpa using h
  have hprev := st289_p67
  have hstep := st289_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p69 : ((2123731847013/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT289 (i+1))
      = (∑ i ∈ Finset.range 68, stT289 (i+1)) + stT289 69 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 68
    simpa using h
  have hprev := st289_p68
  have hstep := st289_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p70 : ((5045165482483/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT289 (i+1))
      = (∑ i ∈ Finset.range 69, stT289 (i+1)) + stT289 70 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 69
    simpa using h
  have hprev := st289_p69
  have hstep := st289_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p71 : ((10618988495321/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT289 (i+1))
      = (∑ i ∈ Finset.range 70, stT289 (i+1)) + stT289 71 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 70
    simpa using h
  have hprev := st289_p70
  have hstep := st289_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p72 : ((10502371786641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT289 (i+1))
      = (∑ i ∈ Finset.range 71, stT289 (i+1)) + stT289 72 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 71
    simpa using h
  have hprev := st289_p71
  have hstep := st289_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p73 : ((10150229928201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT289 (i+1))
      = (∑ i ∈ Finset.range 72, stT289 (i+1)) + stT289 73 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 72
    simpa using h
  have hprev := st289_p72
  have hstep := st289_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p74 : ((10726135650789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT289 (i+1))
      = (∑ i ∈ Finset.range 73, stT289 (i+1)) + stT289 74 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 73
    simpa using h
  have hprev := st289_p73
  have hstep := st289_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p75 : ((5125253112991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT289 (i+1))
      = (∑ i ∈ Finset.range 74, stT289 (i+1)) + stT289 75 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 74
    simpa using h
  have hprev := st289_p74
  have hstep := st289_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p76 : ((10409864610671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT289 (i+1))
      = (∑ i ∈ Finset.range 75, stT289 (i+1)) + stT289 76 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 75
    simpa using h
  have hprev := st289_p75
  have hstep := st289_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p77 : ((10607643058421/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT289 (i+1))
      = (∑ i ∈ Finset.range 76, stT289 (i+1)) + stT289 77 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 76
    simpa using h
  have hprev := st289_p76
  have hstep := st289_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p78 : ((10149704544101/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT289 (i+1))
      = (∑ i ∈ Finset.range 77, stT289 (i+1)) + stT289 78 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 77
    simpa using h
  have hprev := st289_p77
  have hstep := st289_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p79 : ((21419956362157/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT289 (i+1))
      = (∑ i ∈ Finset.range 78, stT289 (i+1)) + stT289 79 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 78
    simpa using h
  have hprev := st289_p78
  have hstep := st289_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p80 : ((4078445640881/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT289 (i+1))
      = (∑ i ∈ Finset.range 79, stT289 (i+1)) + stT289 80 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 79
    simpa using h
  have hprev := st289_p79
  have hstep := st289_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p81 : ((4224510070719/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT289 (i+1))
      = (∑ i ∈ Finset.range 80, stT289 (i+1)) + stT289 81 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 80
    simpa using h
  have hprev := st289_p80
  have hstep := st289_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p82 : ((20782527039931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT289 (i+1))
      = (∑ i ∈ Finset.range 81, stT289 (i+1)) + stT289 82 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 81
    simpa using h
  have hprev := st289_p81
  have hstep := st289_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p83 : ((5060811499/2441406250 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT289 (i+1))
      = (∑ i ∈ Finset.range 82, stT289 (i+1)) + stT289 83 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 82
    simpa using h
  have hprev := st289_p82
  have hstep := st289_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p84 : ((21121619533989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT289 (i+1))
      = (∑ i ∈ Finset.range 83, stT289 (i+1)) + stT289 84 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 83
    simpa using h
  have hprev := st289_p83
  have hstep := st289_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p85 : ((5116989706701/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT289 (i+1))
      = (∑ i ∈ Finset.range 84, stT289 (i+1)) + stT289 85 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 84
    simpa using h
  have hprev := st289_p84
  have hstep := st289_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p86 : ((21302546183359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT289 (i+1))
      = (∑ i ∈ Finset.range 85, stT289 (i+1)) + stT289 86 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 85
    simpa using h
  have hprev := st289_p85
  have hstep := st289_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p87 : ((20354493811267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT289 (i+1))
      = (∑ i ∈ Finset.range 86, stT289 (i+1)) + stT289 87 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 86
    simpa using h
  have hprev := st289_p86
  have hstep := st289_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p88 : ((66764597813/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT289 (i+1))
      = (∑ i ∈ Finset.range 87, stT289 (i+1)) + stT289 88 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 87
    simpa using h
  have hprev := st289_p87
  have hstep := st289_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p89 : ((1016293133009/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT289 (i+1))
      = (∑ i ∈ Finset.range 88, stT289 (i+1)) + stT289 89 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 88
    simpa using h
  have hprev := st289_p88
  have hstep := st289_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p90 : ((667909108349/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT289 (i+1))
      = (∑ i ∈ Finset.range 89, stT289 (i+1)) + stT289 90 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 89
    simpa using h
  have hprev := st289_p89
  have hstep := st289_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p91 : ((20326681849033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT289 (i+1))
      = (∑ i ∈ Finset.range 90, stT289 (i+1)) + stT289 91 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 90
    simpa using h
  have hprev := st289_p90
  have hstep := st289_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p92 : ((21368114317837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT289 (i+1))
      = (∑ i ∈ Finset.range 91, stT289 (i+1)) + stT289 92 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 91
    simpa using h
  have hprev := st289_p91
  have hstep := st289_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p93 : ((20333039200957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT289 (i+1))
      = (∑ i ∈ Finset.range 92, stT289 (i+1)) + stT289 93 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 92
    simpa using h
  have hprev := st289_p92
  have hstep := st289_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p94 : ((21357840540979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT289 (i+1))
      = (∑ i ∈ Finset.range 93, stT289 (i+1)) + stT289 94 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 93
    simpa using h
  have hprev := st289_p93
  have hstep := st289_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p95 : ((1271960658229/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT289 (i+1))
      = (∑ i ∈ Finset.range 94, stT289 (i+1)) + stT289 95 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 94
    simpa using h
  have hprev := st289_p94
  have hstep := st289_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p96 : ((5330714216061/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT289 (i+1))
      = (∑ i ∈ Finset.range 95, stT289 (i+1)) + stT289 96 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 95
    simpa using h
  have hprev := st289_p95
  have hstep := st289_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p97 : ((25515047259/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT289 (i+1))
      = (∑ i ∈ Finset.range 96, stT289 (i+1)) + stT289 97 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 96
    simpa using h
  have hprev := st289_p96
  have hstep := st289_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p98 : ((530623056847/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT289 (i+1))
      = (∑ i ∈ Finset.range 97, stT289 (i+1)) + stT289 98 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 97
    simpa using h
  have hprev := st289_p97
  have hstep := st289_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p99 : ((10278115647999/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT289 (i+1))
      = (∑ i ∈ Finset.range 98, stT289 (i+1)) + stT289 99 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 98
    simpa using h
  have hprev := st289_p98
  have hstep := st289_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p100 : ((21027425824803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT289 (i+1))
      = (∑ i ∈ Finset.range 99, stT289 (i+1)) + stT289 100 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 99
    simpa using h
  have hprev := st289_p99
  have hstep := st289_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p101 : ((20805490559207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT289 (i+1))
      = (∑ i ∈ Finset.range 100, stT289 (i+1)) + stT289 101 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 100
    simpa using h
  have hprev := st289_p100
  have hstep := st289_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p102 : ((20736684184539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT289 (i+1))
      = (∑ i ∈ Finset.range 101, stT289 (i+1)) + stT289 102 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 101
    simpa using h
  have hprev := st289_p101
  have hstep := st289_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p103 : ((21112587198039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT289 (i+1))
      = (∑ i ∈ Finset.range 102, stT289 (i+1)) + stT289 103 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 102
    simpa using h
  have hprev := st289_p102
  have hstep := st289_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p104 : ((20450695023039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT289 (i+1))
      = (∑ i ∈ Finset.range 103, stT289 (i+1)) + stT289 104 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 103
    simpa using h
  have hprev := st289_p103
  have hstep := st289_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p105 : ((21327656329239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT289 (i+1))
      = (∑ i ∈ Finset.range 104, stT289 (i+1)) + stT289 105 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 104
    simpa using h
  have hprev := st289_p104
  have hstep := st289_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p106 : ((20357571810021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT289 (i+1))
      = (∑ i ∈ Finset.range 105, stT289 (i+1)) + stT289 106 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 105
    simpa using h
  have hprev := st289_p105
  have hstep := st289_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p107 : ((21256594720373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT289 (i+1))
      = (∑ i ∈ Finset.range 106, stT289 (i+1)) + stT289 107 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 106
    simpa using h
  have hprev := st289_p106
  have hstep := st289_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p108 : ((824267692779/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT289 (i+1))
      = (∑ i ∈ Finset.range 107, stT289 (i+1)) + stT289 108 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 107
    simpa using h
  have hprev := st289_p107
  have hstep := st289_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p109 : ((20855955042063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT289 (i+1))
      = (∑ i ∈ Finset.range 108, stT289 (i+1)) + stT289 109 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 108
    simpa using h
  have hprev := st289_p108
  have hstep := st289_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p110 : ((4216301393249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT289 (i+1))
      = (∑ i ∈ Finset.range 109, stT289 (i+1)) + stT289 110 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 109
    simpa using h
  have hprev := st289_p109
  have hstep := st289_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p111 : ((20424016677223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT289 (i+1))
      = (∑ i ∈ Finset.range 110, stT289 (i+1)) + stT289 111 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 110
    simpa using h
  have hprev := st289_p110
  have hstep := st289_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p112 : ((1333626995141/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT289 (i+1))
      = (∑ i ∈ Finset.range 111, stT289 (i+1)) + stT289 112 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 111
    simpa using h
  have hprev := st289_p111
  have hstep := st289_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p113 : ((408879677079/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT289 (i+1))
      = (∑ i ∈ Finset.range 112, stT289 (i+1)) + stT289 113 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 112
    simpa using h
  have hprev := st289_p112
  have hstep := st289_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p114 : ((4203451446003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT289 (i+1))
      = (∑ i ∈ Finset.range 113, stT289 (i+1)) + stT289 114 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 113
    simpa using h
  have hprev := st289_p113
  have hstep := st289_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p115 : ((4195737764643/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT289 (i+1))
      = (∑ i ∈ Finset.range 114, stT289 (i+1)) + stT289 115 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 114
    simpa using h
  have hprev := st289_p114
  have hstep := st289_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p116 : ((20455750150321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT289 (i+1))
      = (∑ i ∈ Finset.range 115, stT289 (i+1)) + stT289 116 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 115
    simpa using h
  have hprev := st289_p115
  have hstep := st289_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p117 : ((21335591253321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT289 (i+1))
      = (∑ i ∈ Finset.range 116, stT289 (i+1)) + stT289 117 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 116
    simpa using h
  have hprev := st289_p116
  have hstep := st289_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p118 : ((20477300516671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT289 (i+1))
      = (∑ i ∈ Finset.range 117, stT289 (i+1)) + stT289 118 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 117
    simpa using h
  have hprev := st289_p117
  have hstep := st289_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p119 : ((20914910141119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT289 (i+1))
      = (∑ i ∈ Finset.range 118, stT289 (i+1)) + stT289 119 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 118
    simpa using h
  have hprev := st289_p118
  have hstep := st289_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p120 : ((21118818825889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT289 (i+1))
      = (∑ i ∈ Finset.range 119, stT289 (i+1)) + stT289 120 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 119
    simpa using h
  have hprev := st289_p119
  have hstep := st289_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p121 : ((10184772557299/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT289 (i+1))
      = (∑ i ∈ Finset.range 120, stT289 (i+1)) + stT289 121 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 120
    simpa using h
  have hprev := st289_p120
  have hstep := st289_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p122 : ((10631566236799/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT289 (i+1))
      = (∑ i ∈ Finset.range 121, stT289 (i+1)) + stT289 122 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 121
    simpa using h
  have hprev := st289_p121
  have hstep := st289_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p123 : ((2591697146781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT289 (i+1))
      = (∑ i ∈ Finset.range 122, stT289 (i+1)) + stT289 123 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 122
    simpa using h
  have hprev := st289_p122
  have hstep := st289_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p124 : ((20578106249873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT289 (i+1))
      = (∑ i ∈ Finset.range 123, stT289 (i+1)) + stT289 124 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 123
    simpa using h
  have hprev := st289_p123
  have hstep := st289_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p125 : ((4265565854421/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT289 (i+1))
      = (∑ i ∈ Finset.range 124, stT289 (i+1)) + stT289 125 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 124
    simpa using h
  have hprev := st289_p124
  have hstep := st289_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p126 : ((10233655568973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT289 (i+1))
      = (∑ i ∈ Finset.range 125, stT289 (i+1)) + stT289 126 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 125
    simpa using h
  have hprev := st289_p125
  have hstep := st289_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p127 : ((10427236717153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT289 (i+1))
      = (∑ i ∈ Finset.range 126, stT289 (i+1)) + stT289 127 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 126
    simpa using h
  have hprev := st289_p126
  have hstep := st289_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p128 : ((21217462085331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT289 (i+1))
      = (∑ i ∈ Finset.range 127, stT289 (i+1)) + stT289 128 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 127
    simpa using h
  have hprev := st289_p127
  have hstep := st289_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p129 : ((20365384499257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT289 (i+1))
      = (∑ i ∈ Finset.range 128, stT289 (i+1)) + stT289 129 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 128
    simpa using h
  have hprev := st289_p128
  have hstep := st289_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p130 : ((4212171457599/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT289 (i+1))
      = (∑ i ∈ Finset.range 129, stT289 (i+1)) + stT289 130 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 129
    simpa using h
  have hprev := st289_p129
  have hstep := st289_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p131 : ((21070552781283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT289 (i+1))
      = (∑ i ∈ Finset.range 130, stT289 (i+1)) + stT289 131 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 130
    simpa using h
  have hprev := st289_p130
  have hstep := st289_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p132 : ((20359925423011/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT289 (i+1))
      = (∑ i ∈ Finset.range 131, stT289 (i+1)) + stT289 132 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 131
    simpa using h
  have hprev := st289_p131
  have hstep := st289_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p133 : ((21175937423859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT289 (i+1))
      = (∑ i ∈ Finset.range 132, stT289 (i+1)) + stT289 133 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 132
    simpa using h
  have hprev := st289_p132
  have hstep := st289_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p134 : ((20962724188231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT289 (i+1))
      = (∑ i ∈ Finset.range 133, stT289 (i+1)) + stT289 134 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 133
    simpa using h
  have hprev := st289_p133
  have hstep := st289_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p135 : ((2038001488607/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT289 (i+1))
      = (∑ i ∈ Finset.range 134, stT289 (i+1)) + stT289 135 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 134
    simpa using h
  have hprev := st289_p134
  have hstep := st289_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p136 : ((10611663699179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT289 (i+1))
      = (∑ i ∈ Finset.range 135, stT289 (i+1)) + stT289 136 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 135
    simpa using h
  have hprev := st289_p135
  have hstep := st289_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p137 : ((2614795645577/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT289 (i+1))
      = (∑ i ∈ Finset.range 136, stT289 (i+1)) + stT289 137 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 136
    simpa using h
  have hprev := st289_p136
  have hstep := st289_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p138 : ((20386405301489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT289 (i+1))
      = (∑ i ∈ Finset.range 137, stT289 (i+1)) + stT289 138 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 137
    simpa using h
  have hprev := st289_p137
  have hstep := st289_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p139 : ((21223806894693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT289 (i+1))
      = (∑ i ∈ Finset.range 138, stT289 (i+1)) + stT289 139 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 138
    simpa using h
  have hprev := st289_p138
  have hstep := st289_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p140 : ((20940375713893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT289 (i+1))
      = (∑ i ∈ Finset.range 139, stT289 (i+1)) + stT289 140 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 139
    simpa using h
  have hprev := st289_p139
  have hstep := st289_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p141 : ((20370710415013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT289 (i+1))
      = (∑ i ∈ Finset.range 140, stT289 (i+1)) + stT289 141 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 140
    simpa using h
  have hprev := st289_p140
  have hstep := st289_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p142 : ((10589572331177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT289 (i+1))
      = (∑ i ∈ Finset.range 141, stT289 (i+1)) + stT289 142 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 141
    simpa using h
  have hprev := st289_p141
  have hstep := st289_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p143 : ((21024306744717/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT289 (i+1))
      = (∑ i ∈ Finset.range 142, stT289 (i+1)) + stT289 143 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 142
    simpa using h
  have hprev := st289_p142
  have hstep := st289_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p144 : ((814020148227/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT289 (i+1))
      = (∑ i ∈ Finset.range 143, stT289 (i+1)) + stT289 144 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 143
    simpa using h
  have hprev := st289_p143
  have hstep := st289_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p145 : ((21074257653939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT289 (i+1))
      = (∑ i ∈ Finset.range 144, stT289 (i+1)) + stT289 145 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 144
    simpa using h
  have hprev := st289_p144
  have hstep := st289_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p146 : ((1322136992679/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT289 (i+1))
      = (∑ i ∈ Finset.range 145, stT289 (i+1)) + stT289 146 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 145
    simpa using h
  have hprev := st289_p145
  have hstep := st289_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p147 : ((20367401995167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT289 (i+1))
      = (∑ i ∈ Finset.range 146, stT289 (i+1)) + stT289 147 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 146
    simpa using h
  have hprev := st289_p146
  have hstep := st289_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p148 : ((4178564440791/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT289 (i+1))
      = (∑ i ∈ Finset.range 147, stT289 (i+1)) + stT289 148 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 147
    simpa using h
  have hprev := st289_p147
  have hstep := st289_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p149 : ((21286828076481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT289 (i+1))
      = (∑ i ∈ Finset.range 148, stT289 (i+1)) + stT289 149 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 148
    simpa using h
  have hprev := st289_p148
  have hstep := st289_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p150 : ((4095637482123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT289 (i+1))
      = (∑ i ∈ Finset.range 149, stT289 (i+1)) + stT289 150 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 149
    simpa using h
  have hprev := st289_p149
  have hstep := st289_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p151 : ((20647701078591/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT289 (i+1))
      = (∑ i ∈ Finset.range 150, stT289 (i+1)) + stT289 151 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 150
    simpa using h
  have hprev := st289_p150
  have hstep := st289_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p152 : ((21340483789431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT289 (i+1))
      = (∑ i ∈ Finset.range 151, stT289 (i+1)) + stT289 152 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 151
    simpa using h
  have hprev := st289_p151
  have hstep := st289_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p153 : ((647560537737/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT289 (i+1))
      = (∑ i ∈ Finset.range 152, stT289 (i+1)) + stT289 153 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 152
    simpa using h
  have hprev := st289_p152
  have hstep := st289_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p154 : ((16333702569/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT289 (i+1))
      = (∑ i ∈ Finset.range 153, stT289 (i+1)) + stT289 154 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 153
    simpa using h
  have hprev := st289_p153
  have hstep := st289_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p155 : ((41439756287/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT289 (i+1))
      = (∑ i ∈ Finset.range 154, stT289 (i+1)) + stT289 155 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 154
    simpa using h
  have hprev := st289_p154
  have hstep := st289_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p156 : ((5264565001521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT289 (i+1))
      = (∑ i ∈ Finset.range 155, stT289 (i+1)) + stT289 156 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 155
    simpa using h
  have hprev := st289_p155
  have hstep := st289_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p157 : ((20348644940469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT289 (i+1))
      = (∑ i ∈ Finset.range 156, stT289 (i+1)) + stT289 157 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 156
    simpa using h
  have hprev := st289_p156
  have hstep := st289_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p158 : ((5221200457373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT289 (i+1))
      = (∑ i ∈ Finset.range 157, stT289 (i+1)) + stT289 158 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 157
    simpa using h
  have hprev := st289_p157
  have hstep := st289_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p159 : ((1065919250831/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT289 (i+1))
      = (∑ i ∈ Finset.range 158, stT289 (i+1)) + stT289 159 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 158
    simpa using h
  have hprev := st289_p158
  have hstep := st289_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p160 : ((411446466341/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT289 (i+1))
      = (∑ i ∈ Finset.range 159, stT289 (i+1)) + stT289 160 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 159
    simpa using h
  have hprev := st289_p159
  have hstep := st289_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p161 : ((20487580105553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT289 (i+1))
      = (∑ i ∈ Finset.range 160, stT289 (i+1)) + stT289 161 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 160
    simpa using h
  have hprev := st289_p160
  have hstep := st289_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p162 : ((21268335000639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT289 (i+1))
      = (∑ i ∈ Finset.range 161, stT289 (i+1)) + stT289 162 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 161
    simpa using h
  have hprev := st289_p161
  have hstep := st289_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p163 : ((21022807741491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT289 (i+1))
      = (∑ i ∈ Finset.range 162, stT289 (i+1)) + stT289 163 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 162
    simpa using h
  have hprev := st289_p162
  have hstep := st289_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p164 : ((635729571693/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT289 (i+1))
      = (∑ i ∈ Finset.range 163, stT289 (i+1)) + stT289 164 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 163
    simpa using h
  have hprev := st289_p163
  have hstep := st289_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p165 : ((10422859030029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT289 (i+1))
      = (∑ i ∈ Finset.range 164, stT289 (i+1)) + stT289 165 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 164
    simpa using h
  have hprev := st289_p164
  have hstep := st289_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p166 : ((5335491465427/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT289 (i+1))
      = (∑ i ∈ Finset.range 165, stT289 (i+1)) + stT289 166 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 165
    simpa using h
  have hprev := st289_p165
  have hstep := st289_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p167 : ((5168443950531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT289 (i+1))
      = (∑ i ∈ Finset.range 166, stT289 (i+1)) + stT289 167 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 166
    simpa using h
  have hprev := st289_p166
  have hstep := st289_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p168 : ((20391629720673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT289 (i+1))
      = (∑ i ∈ Finset.range 167, stT289 (i+1)) + stT289 168 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 167
    simpa using h
  have hprev := st289_p167
  have hstep := st289_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p169 : ((21140540510223/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT289 (i+1))
      = (∑ i ∈ Finset.range 168, stT289 (i+1)) + stT289 169 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 168
    simpa using h
  have hprev := st289_p168
  have hstep := st289_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p170 : ((21213752592771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT289 (i+1))
      = (∑ i ∈ Finset.range 169, stT289 (i+1)) + stT289 170 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 169
    simpa using h
  have hprev := st289_p169
  have hstep := st289_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p171 : ((20449267361811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT289 (i+1))
      = (∑ i ∈ Finset.range 170, stT289 (i+1)) + stT289 171 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 170
    simpa using h
  have hprev := st289_p170
  have hstep := st289_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p172 : ((20557741761207/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT289 (i+1))
      = (∑ i ∈ Finset.range 171, stT289 (i+1)) + stT289 172 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 171
    simpa using h
  have hprev := st289_p171
  have hstep := st289_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p173 : ((5323699823543/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT289 (i+1))
      = (∑ i ∈ Finset.range 172, stT289 (i+1)) + stT289 173 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 172
    simpa using h
  have hprev := st289_p172
  have hstep := st289_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p174 : ((1315015300747/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT289 (i+1))
      = (∑ i ∈ Finset.range 173, stT289 (i+1)) + stT289 174 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 173
    simpa using h
  have hprev := st289_p173
  have hstep := st289_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p175 : ((20352333547443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT289 (i+1))
      = (∑ i ∈ Finset.range 174, stT289 (i+1)) + stT289 175 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 174
    simpa using h
  have hprev := st289_p174
  have hstep := st289_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p176 : ((20716036708889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT289 (i+1))
      = (∑ i ∈ Finset.range 175, stT289 (i+1)) + stT289 176 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 175
    simpa using h
  have hprev := st289_p175
  have hstep := st289_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p177 : ((21348672342771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT289 (i+1))
      = (∑ i ∈ Finset.range 176, stT289 (i+1)) + stT289 177 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 176
    simpa using h
  have hprev := st289_p176
  have hstep := st289_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p178 : ((20908457208531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT289 (i+1))
      = (∑ i ∈ Finset.range 177, stT289 (i+1)) + stT289 178 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 177
    simpa using h
  have hprev := st289_p177
  have hstep := st289_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p179 : ((4065053904419/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT289 (i+1))
      = (∑ i ∈ Finset.range 178, stT289 (i+1)) + stT289 179 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 178
    simpa using h
  have hprev := st289_p178
  have hstep := st289_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p180 : ((4162785150161/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT289 (i+1))
      = (∑ i ∈ Finset.range 179, stT289 (i+1)) + stT289 180 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 179
    simpa using h
  have hprev := st289_p179
  have hstep := st289_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p181 : ((21360019392841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT289 (i+1))
      = (∑ i ∈ Finset.range 180, stT289 (i+1)) + stT289 181 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 180
    simpa using h
  have hprev := st289_p180
  have hstep := st289_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p182 : ((20845581515341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT289 (i+1))
      = (∑ i ∈ Finset.range 181, stT289 (i+1)) + stT289 182 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 181
    simpa using h
  have hprev := st289_p181
  have hstep := st289_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p183 : ((20319823913059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT289 (i+1))
      = (∑ i ∈ Finset.range 182, stT289 (i+1)) + stT289 183 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 182
    simpa using h
  have hprev := st289_p182
  have hstep := st289_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p184 : ((20840216797323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT289 (i+1))
      = (∑ i ∈ Finset.range 183, stT289 (i+1)) + stT289 184 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 183
    simpa using h
  have hprev := st289_p183
  have hstep := st289_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p185 : ((21363106140621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT289 (i+1))
      = (∑ i ∈ Finset.range 184, stT289 (i+1)) + stT289 185 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 184
    simpa using h
  have hprev := st289_p184
  have hstep := st289_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p186 : ((20854401668541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT289 (i+1))
      = (∑ i ∈ Finset.range 185, stT289 (i+1)) + stT289 186 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 185
    simpa using h
  have hprev := st289_p185
  have hstep := st289_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p187 : ((4063396073113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT289 (i+1))
      = (∑ i ∈ Finset.range 186, stT289 (i+1)) + stT289 187 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 186
    simpa using h
  have hprev := st289_p186
  have hstep := st289_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p188 : ((20795579548817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT289 (i+1))
      = (∑ i ∈ Finset.range 187, stT289 (i+1)) + stT289 188 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 187
    simpa using h
  have hprev := st289_p187
  have hstep := st289_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p189 : ((21361878224753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT289 (i+1))
      = (∑ i ∈ Finset.range 188, stT289 (i+1)) + stT289 189 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 188
    simpa using h
  have hprev := st289_p188
  have hstep := st289_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p190 : ((2093288989059/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT289 (i+1))
      = (∑ i ∈ Finset.range 189, stT289 (i+1)) + stT289 190 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 189
    simpa using h
  have hprev := st289_p189
  have hstep := st289_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p191 : ((4065423593123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT289 (i+1))
      = (∑ i ∈ Finset.range 190, stT289 (i+1)) + stT289 191 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 190
    simpa using h
  have hprev := st289_p190
  have hstep := st289_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p192 : ((10341935832693/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT289 (i+1))
      = (∑ i ∈ Finset.range 191, stT289 (i+1)) + stT289 192 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 191
    simpa using h
  have hprev := st289_p191
  have hstep := st289_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p193 : ((10666339177633/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT289 (i+1))
      = (∑ i ∈ Finset.range 192, stT289 (i+1)) + stT289 193 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 192
    simpa using h
  have hprev := st289_p192
  have hstep := st289_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p194 : ((21072687452391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT289 (i+1))
      = (∑ i ∈ Finset.range 193, stT289 (i+1)) + stT289 194 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 193
    simpa using h
  have hprev := st289_p193
  have hstep := st289_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p195 : ((10192744946103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT289 (i+1))
      = (∑ i ∈ Finset.range 194, stT289 (i+1)) + stT289 195 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 194
    simpa using h
  have hprev := st289_p194
  have hstep := st289_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p196 : ((20522403326721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT289 (i+1))
      = (∑ i ∈ Finset.range 195, stT289 (i+1)) + stT289 196 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 195
    simpa using h
  have hprev := st289_p195
  have hstep := st289_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p197 : ((21231727771671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT289 (i+1))
      = (∑ i ∈ Finset.range 196, stT289 (i+1)) + stT289 197 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 196
    simpa using h
  have hprev := st289_p196
  have hstep := st289_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p198 : ((21242013994777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT289 (i+1))
      = (∑ i ∈ Finset.range 197, stT289 (i+1)) + stT289 198 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 197
    simpa using h
  have hprev := st289_p197
  have hstep := st289_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p199 : ((20538992322271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT289 (i+1))
      = (∑ i ∈ Finset.range 198, stT289 (i+1)) + stT289 199 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 198
    simpa using h
  have hprev := st289_p198
  have hstep := st289_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p200 : ((2036286398939/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT289 (i+1))
      = (∑ i ∈ Finset.range 199, stT289 (i+1)) + stT289 200 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 199
    simpa using h
  have hprev := st289_p199
  have hstep := st289_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p201 : ((4203511491919/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT289 (i+1))
      = (∑ i ∈ Finset.range 200, stT289 (i+1)) + stT289 201 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 200
    simpa using h
  have hprev := st289_p200
  have hstep := st289_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p202 : ((21365615637943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT289 (i+1))
      = (∑ i ∈ Finset.range 201, stT289 (i+1)) + stT289 202 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 201
    simpa using h
  have hprev := st289_p201
  have hstep := st289_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p203 : ((10405801092241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT289 (i+1))
      = (∑ i ∈ Finset.range 202, stT289 (i+1)) + stT289 203 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 202
    simpa using h
  have hprev := st289_p202
  have hstep := st289_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p204 : ((20303530164871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT289 (i+1))
      = (∑ i ∈ Finset.range 203, stT289 (i+1)) + stT289 204 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 203
    simpa using h
  have hprev := st289_p203
  have hstep := st289_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p205 : ((20698598491231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT289 (i+1))
      = (∑ i ∈ Finset.range 204, stT289 (i+1)) + stT289 205 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 204
    simpa using h
  have hprev := st289_p204
  have hstep := st289_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p206 : ((21329821867639/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT289 (i+1))
      = (∑ i ∈ Finset.range 205, stT289 (i+1)) + stT289 206 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 205
    simpa using h
  have hprev := st289_p205
  have hstep := st289_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p207 : ((21147313121023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT289 (i+1))
      = (∑ i ∈ Finset.range 206, stT289 (i+1)) + stT289 207 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 206
    simpa using h
  have hprev := st289_p206
  have hstep := st289_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p208 : ((4091304960051/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT289 (i+1))
      = (∑ i ∈ Finset.range 207, stT289 (i+1)) + stT289 208 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 207
    simpa using h
  have hprev := st289_p207
  have hstep := st289_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p209 : ((4077876835099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT289 (i+1))
      = (∑ i ∈ Finset.range 208, stT289 (i+1)) + stT289 209 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 208
    simpa using h
  have hprev := st289_p208
  have hstep := st289_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p210 : ((842034998559/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT289 (i+1))
      = (∑ i ∈ Finset.range 209, stT289 (i+1)) + stT289 210 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 209
    simpa using h
  have hprev := st289_p209
  have hstep := st289_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p211 : ((4274509966251/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT289 (i+1))
      = (∑ i ∈ Finset.range 210, stT289 (i+1)) + stT289 211 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 210
    simpa using h
  have hprev := st289_p210
  have hstep := st289_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p212 : ((20843083783313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT289 (i+1))
      = (∑ i ∈ Finset.range 211, stT289 (i+1)) + stT289 212 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 211
    simpa using h
  have hprev := st289_p211
  have hstep := st289_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p213 : ((10152831664121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT289 (i+1))
      = (∑ i ∈ Finset.range 212, stT289 (i+1)) + stT289 213 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 212
    simpa using h
  have hprev := st289_p212
  have hstep := st289_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p214 : ((5151067757363/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT289 (i+1))
      = (∑ i ∈ Finset.range 213, stT289 (i+1)) + stT289 214 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 213
    simpa using h
  have hprev := st289_p213
  have hstep := st289_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p215 : ((531710976757/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT289 (i+1))
      = (∑ i ∈ Finset.range 214, stT289 (i+1)) + stT289 215 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 214
    simpa using h
  have hprev := st289_p214
  have hstep := st289_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p216 : ((21269065730653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT289 (i+1))
      = (∑ i ∈ Finset.range 215, stT289 (i+1)) + stT289 216 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 215
    simpa using h
  have hprev := st289_p215
  have hstep := st289_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p217 : ((5152280452997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT289 (i+1))
      = (∑ i ∈ Finset.range 216, stT289 (i+1)) + stT289 217 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 216
    simpa using h
  have hprev := st289_p216
  have hstep := st289_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p218 : ((10148444112493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT289 (i+1))
      = (∑ i ∈ Finset.range 217, stT289 (i+1)) + stT289 218 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 217
    simpa using h
  have hprev := st289_p217
  have hstep := st289_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p219 : ((2600205774353/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT289 (i+1))
      = (∑ i ∈ Finset.range 218, stT289 (i+1)) + stT289 219 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 218
    simpa using h
  have hprev := st289_p218
  have hstep := st289_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p220 : ((10680996604847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT289 (i+1))
      = (∑ i ∈ Finset.range 219, stT289 (i+1)) + stT289 220 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 219
    simpa using h
  have hprev := st289_p219
  have hstep := st289_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p221 : ((1321522538957/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT289 (i+1))
      = (∑ i ∈ Finset.range 220, stT289 (i+1)) + stT289 221 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 220
    simpa using h
  have hprev := st289_p220
  have hstep := st289_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p222 : ((20474479492769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT289 (i+1))
      = (∑ i ∈ Finset.range 221, stT289 (i+1)) + stT289 222 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 221
    simpa using h
  have hprev := st289_p221
  have hstep := st289_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p223 : ((20335711271519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT289 (i+1))
      = (∑ i ∈ Finset.range 222, stT289 (i+1)) + stT289 223 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 222
    simpa using h
  have hprev := st289_p222
  have hstep := st289_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p224 : ((20926318434339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT289 (i+1))
      = (∑ i ∈ Finset.range 223, stT289 (i+1)) + stT289 224 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 223
    simpa using h
  have hprev := st289_p223
  have hstep := st289_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p225 : ((4278052394079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT289 (i+1))
      = (∑ i ∈ Finset.range 224, stT289 (i+1)) + stT289 225 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 224
    simpa using h
  have hprev := st289_p224
  have hstep := st289_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p226 : ((131652800579/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT289 (i+1))
      = (∑ i ∈ Finset.range 225, stT289 (i+1)) + stT289 226 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 225
    simpa using h
  have hprev := st289_p225
  have hstep := st289_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p227 : ((1276013131313/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT289 (i+1))
      = (∑ i ∈ Finset.range 226, stT289 (i+1)) + stT289 227 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 226
    simpa using h
  have hprev := st289_p226
  have hstep := st289_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p228 : ((10180433548443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT289 (i+1))
      = (∑ i ∈ Finset.range 227, stT289 (i+1)) + stT289 228 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 227
    simpa using h
  have hprev := st289_p227
  have hstep := st289_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p229 : ((2621512907691/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT289 (i+1))
      = (∑ i ∈ Finset.range 228, stT289 (i+1)) + stT289 229 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 228
    simpa using h
  have hprev := st289_p228
  have hstep := st289_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p230 : ((2674673112361/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT289 (i+1))
      = (∑ i ∈ Finset.range 229, stT289 (i+1)) + stT289 230 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 229
    simpa using h
  have hprev := st289_p229
  have hstep := st289_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p231 : ((2631489173037/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT289 (i+1))
      = (∑ i ∈ Finset.range 230, stT289 (i+1)) + stT289 231 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 230
    simpa using h
  have hprev := st289_p230
  have hstep := st289_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p232 : ((10206320318433/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT289 (i+1))
      = (∑ i ∈ Finset.range 231, stT289 (i+1)) + stT289 232 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 231
    simpa using h
  have hprev := st289_p231
  have hstep := st289_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p233 : ((5087195654979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT289 (i+1))
      = (∑ i ∈ Finset.range 232, stT289 (i+1)) + stT289 233 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 232
    simpa using h
  have hprev := st289_p232
  have hstep := st289_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p234 : ((5235688970129/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT289 (i+1))
      = (∑ i ∈ Finset.range 233, stT289 (i+1)) + stT289 234 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 233
    simpa using h
  have hprev := st289_p233
  have hstep := st289_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p235 : ((5349083798697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT289 (i+1))
      = (∑ i ∈ Finset.range 234, stT289 (i+1)) + stT289 235 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 234
    simpa using h
  have hprev := st289_p234
  have hstep := st289_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p236 : ((5277087979807/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT289 (i+1))
      = (∑ i ∈ Finset.range 235, stT289 (i+1)) + stT289 236 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 235
    simpa using h
  have hprev := st289_p235
  have hstep := st289_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p237 : ((10231298421919/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT289 (i+1))
      = (∑ i ∈ Finset.range 236, stT289 (i+1)) + stT289 237 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 236
    simpa using h
  have hprev := st289_p236
  have hstep := st289_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p238 : ((2030555192333/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT289 (i+1))
      = (∑ i ∈ Finset.range 237, stT289 (i+1)) + stT289 238 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 237
    simpa using h
  have hprev := st289_p237
  have hstep := st289_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p239 : ((520950322773/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT289 (i+1))
      = (∑ i ∈ Finset.range 238, stT289 (i+1)) + stT289 239 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 238
    simpa using h
  have hprev := st289_p238
  have hstep := st289_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p240 : ((21369591954863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT289 (i+1))
      = (∑ i ∈ Finset.range 239, stT289 (i+1)) + stT289 240 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 239
    simpa using h
  have hprev := st289_p239
  have hstep := st289_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p241 : ((21220229982959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT289 (i+1))
      = (∑ i ∈ Finset.range 240, stT289 (i+1)) + stT289 241 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 240
    simpa using h
  have hprev := st289_p240
  have hstep := st289_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p242 : ((2572956092773/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT289 (i+1))
      = (∑ i ∈ Finset.range 241, stT289 (i+1)) + stT289 242 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 241
    simpa using h
  have hprev := st289_p241
  have hstep := st289_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p243 : ((5066312816963/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT289 (i+1))
      = (∑ i ∈ Finset.range 242, stT289 (i+1)) + stT289 243 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 242
    simpa using h
  have hprev := st289_p242
  have hstep := st289_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p244 : ((1033076642303/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT289 (i+1))
      = (∑ i ∈ Finset.range 243, stT289 (i+1)) + stT289 244 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 243
    simpa using h
  have hprev := st289_p243
  have hstep := st289_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p245 : ((332432398187/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT289 (i+1))
      = (∑ i ∈ Finset.range 244, stT289 (i+1)) + stT289 245 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 244
    simpa using h
  have hprev := st289_p244
  have hstep := st289_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p246 : ((2668579311691/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT289 (i+1))
      = (∑ i ∈ Finset.range 245, stT289 (i+1)) + stT289 246 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 245
    simpa using h
  have hprev := st289_p245
  have hstep := st289_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p247 : ((20794243827023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT289 (i+1))
      = (∑ i ∈ Finset.range 246, stT289 (i+1)) + stT289 247 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 246
    simpa using h
  have hprev := st289_p246
  have hstep := st289_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p248 : ((811616142143/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT289 (i+1))
      = (∑ i ∈ Finset.range 247, stT289 (i+1)) + stT289 248 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 247
    simpa using h
  have hprev := st289_p247
  have hstep := st289_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p249 : ((20445084174943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT289 (i+1))
      = (∑ i ∈ Finset.range 248, stT289 (i+1)) + stT289 249 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 248
    simpa using h
  have hprev := st289_p248
  have hstep := st289_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_p250 : ((21068804971393/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT289 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT289 (i+1))
      = (∑ i ∈ Finset.range 249, stT289 (i+1)) + stT289 250 := by
    have h := Finset.sum_range_succ (fun i => stT289 (i+1)) 249
    simpa using h
  have hprev := st289_p249
  have hstep := st289_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st289_s250 :
    |Real.sin (((289 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))
      - ((-165021/1000000 : ℚ) : ℝ)| ≤ ((1/10000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -414449/10000000) (δ := 7289/500000000) (ψ := -30537/500000) 289 254
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 289`** (evaluated boundary). -/
theorem station_289_sign : 0 < hardyG ((((289:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 289 250 (by norm_num) (by norm_num)
    ((-30537/500000 : ℚ) : ℝ)
  have hchain := st289_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT289 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((289 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-30537/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st289_c250
  have hsinb := abs_le.mp st289_s250
  have hbdy_lo : ((2983225345117/334085000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((289 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-30537/500000 : ℚ) : ℝ))) / 2
          - ((((289:ℕ)):ℝ))
            * Real.sin (((289 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-30537/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((289:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((289:ℝ) * Real.log (250:ℝ) - ((-30537/500000 : ℚ) : ℝ))) / 2
        - ((289:ℝ)) * Real.sin ((289:ℝ) * Real.log (250:ℝ) - ((-30537/500000 : ℚ) : ℝ))
        ≥ ((23584487/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((289:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((23584487/500000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((23584487/500000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((23584487/500000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((289:ℕ)):ℝ))+1) * (((((289:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((113837257523/62500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((21068804971393/10000000000000 : ℚ) : ℝ) + ((2983225345117/334085000000000 : ℚ) : ℝ)
      - ((113837257523/62500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-30537/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((289:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-30537/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((289:ℕ)):ℝ)))).re
      - Real.sin ((-30537/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((289:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((289:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((289:ℕ)):ℝ))
      = (((((289:ℕ)):ℝ)) * (Real.log ((((289:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((289:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_289
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
  have hθwin : |(((-30537/500000 : ℚ) : ℝ) + ((65:ℤ)) * (2*Real.pi)) - theta ((((289:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((289:ℕ)):ℝ)))
    (φ := ((-30537/500000 : ℚ) : ℝ) + ((65:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-30537/500000 : ℚ)) : ℝ) 65).1,
    (cos_sin_shift (((-30537/500000 : ℚ)) : ℝ) 65).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_289_sign
end AxiomAudit
