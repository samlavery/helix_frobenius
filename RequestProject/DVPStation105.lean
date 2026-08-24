import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 105` (rung-109; evaluated boundary, N = 200)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT105 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((105 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((176023/250000 : ℚ) : ℝ))

theorem st105_c1 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((762199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1760231/10000000) (δ := 41/100000000) (ψ := 176023/250000) 105 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t1 : ((762149/1000000 : ℚ) : ℝ) ≤ stT105 1 := by
  have hc : ((762149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((762149/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((762149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c2 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-196759/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1850827/2500000) (δ := 809/100000000) (ψ := 176023/250000) 105 11
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t2 : ((-347841744823/500000000000 : ℚ) : ℝ) ≤ stT105 2 := by
  have hc : ((-196769/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-347841744823/500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-196769/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c3 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((17933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970539/2500000) (δ := 447/50000000) (ψ := 176023/250000) 105 18
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t3 : ((51623768133/5000000000000 : ℚ) : ℝ) ≤ stT105 3 := by
  have hc : ((17883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51623768133/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((17883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c4 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((235391/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214721/2500000) (δ := 309/50000000) (ψ := 176023/250000) 105 23
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t4 : ((470757/1000000 : ℚ) : ℝ) ≤ stT105 4 := by
  have hc : ((470757/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((470757/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((470757/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c5 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((26263/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3397787/10000000) (δ := 119/12500000) (ψ := 176023/250000) 105 27
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t5 : ((93938984529/1000000000000 : ℚ) : ℝ) ≤ stT105 5 := by
  have hc : ((105027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93938984529/1000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((105027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c6 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((96917/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -665567/2500000) (δ := 703/100000000) (ψ := 176023/250000) 105 30
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t6 : ((197810541587/1000000000000 : ℚ) : ℝ) ≤ stT105 6 := by
  have hc : ((96907/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197810541587/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((96907/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c7 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-832579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6386359/10000000) (δ := 559/100000000) (ψ := 176023/250000) 105 32
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t7 : ((-629408407341/2000000000000 : ℚ) : ℝ) ≤ stT105 7 := by
  have hc : ((-832629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-629408407341/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-832629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c8 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-646829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284277/500000) (δ := 313/50000000) (ψ := 176023/250000) 105 35
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t8 : ((-1143531349193/5000000000000 : ℚ) : ℝ) ≤ stT105 8 := by
  have hc : ((-646879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1143531349193/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-646879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c9 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-784923/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -309171/500000) (δ := 197/25000000) (ψ := 176023/250000) 105 37
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t9 : ((-1308288594991/5000000000000 : ℚ) : ℝ) ≤ stT105 9 := by
  have hc : ((-784973/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1308288594991/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-784973/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c10 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-670961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 720719/1250000) (δ := 949/100000000) (ψ := 176023/250000) 105 38
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t10 : ((-1060961661529/5000000000000 : ℚ) : ℝ) ≤ stT105 10 := by
  have hc : ((-671011/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1060961661529/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-671011/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c11 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((968291/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157813/2500000) (δ := 3/400000) (ψ := 176023/250000) 105 40
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t11 : ((2919356026233/10000000000000 : ℚ) : ℝ) ≤ stT105 11 := by
  have hc : ((968241/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2919356026233/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((968241/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c12 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-857151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6501271/10000000) (δ := 69/12500000) (ψ := 176023/250000) 105 41
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t12 : ((-77328959411/312500000000 : ℚ) : ℝ) ≤ stT105 12 := by
  have hc : ((-857201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77328959411/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-857201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c13 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((4709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -780689/2000000) (δ := 143/25000000) (ψ := 176023/250000) 105 43
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t13 : ((6495537/2500000000 : ℚ) : ℝ) ≤ stT105 13 := by
  have hc : ((1171/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6495537/2500000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((1171/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c14 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((499001/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31613/2000000) (δ := 3/400000) (ψ := 176023/250000) 105 44
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t14 : ((10418509729/39062500000 : ℚ) : ℝ) ≤ stT105 14 := by
  have hc : ((15593/15625 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((10418509729/39062500000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((15593/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c15 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((623301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 11223/50000) (δ := 1069/100000000) (ψ := 176023/250000) 105 45
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t15 : ((402306650747/2500000000000 : ℚ) : ℝ) ≤ stT105 15 := by
  have hc : ((623251/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402306650747/2500000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((623251/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c16 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((178633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3477999/10000000) (δ := 207/25000000) (ψ := 176023/250000) 105 46
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t16 : ((178583/4000000 : ℚ) : ℝ) ≤ stT105 16 := by
  have hc : ((178583/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((178583/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((178583/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c17 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((24261/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3683999/10000000) (δ := 299/50000000) (ψ := 176023/250000) 105 47
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t17 : ((29405622483/1250000000000 : ℚ) : ℝ) ≤ stT105 17 := by
  have hc : ((48497/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29405622483/1250000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((48497/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c18 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((184879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2980119/10000000) (δ := 293/50000000) (ψ := 176023/250000) 105 48
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t18 : ((108926236197/1250000000000 : ℚ) : ℝ) ≤ stT105 18 := by
  have hc : ((92427/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((108926236197/1250000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((92427/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c19 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((833203/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1464801/10000000) (δ := 797/100000000) (ψ := 176023/250000) 105 49
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t19 : ((1911383787021/10000000000000 : ℚ) : ℝ) ≤ stT105 19 := by
  have hc : ((833153/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1911383787021/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((833153/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c20 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((237971/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -48667/625000) (δ := 757/100000000) (ψ := 176023/250000) 105 50
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t20 : ((1064182298439/5000000000000 : ℚ) : ℝ) ≤ stT105 20 := by
  have hc : ((475917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1064182298439/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((475917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c21 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((98947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3679217/10000000) (δ := 133/20000000) (ψ := 176023/250000) 105 51
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t21 : ((107905428833/5000000000000 : ℚ) : ℝ) ≤ stT105 21 := by
  have hc : ((98897/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107905428833/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((98897/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c22 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-963417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1793919/2500000) (δ := 559/100000000) (ψ := 176023/250000) 105 52
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t22 : ((-256764918967/1250000000000 : ℚ) : ℝ) ≤ stT105 22 := by
  have hc : ((-963467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256764918967/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-963467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c23 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-5611/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4492911/10000000) (δ := 457/50000000) (ψ := 176023/250000) 105 52
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t23 : ((-9361884021/200000000000 : ℚ) : ℝ) ≤ stT105 23 := by
  have hc : ((-22449/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9361884021/200000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-22449/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c24 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((999851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43153/10000000) (δ := 743/100000000) (ψ := 176023/250000) 105 53
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t24 : ((2040834793041/10000000000000 : ℚ) : ℝ) ≤ stT105 24 := by
  have hc : ((999801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2040834793041/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((999801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c25 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-2681/6250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5035343/10000000) (δ := 813/100000000) (ψ := 176023/250000) 105 54
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t25 : ((-85802042901/1000000000000 : ℚ) : ℝ) ≤ stT105 25 := by
  have hc : ((-42901/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85802042901/1000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-42901/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c26 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-508327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2630047/5000000) (δ := 683/100000000) (ψ := 176023/250000) 105 54
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t26 : ((-498504827037/5000000000000 : ℚ) : ℝ) ≤ stT105 26 := by
  have hc : ((-508377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-498504827037/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-508377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c27 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((488337/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -541033/10000000) (δ := 671/100000000) (ψ := 176023/250000) 105 55
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t27 : ((234939111/1250000000 : ℚ) : ℝ) ≤ stT105 27 := by
  have hc : ((61039/62500 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((234939111/1250000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((61039/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c28 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-895787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -670249/1000000) (δ := 981/100000000) (ψ := 176023/250000) 105 56
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t28 : ((-1692973366851/10000000000000 : ℚ) : ℝ) ≤ stT105 28 := by
  have hc : ((-895837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1692973366851/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-895837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c29 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((134319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1254491/5000000) (δ := 751/100000000) (ψ := 176023/250000) 105 56
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t29 : ((498801716189/5000000000000 : ℚ) : ℝ) ≤ stT105 29 := by
  have hc : ((268613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((498801716189/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((268613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c30 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-148581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268739/625000) (δ := 421/50000000) (ψ := 176023/250000) 105 57
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t30 : ((-135680929601/5000000000000 : ℚ) : ℝ) ≤ stT105 30 := by
  have hc : ((-148631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-135680929601/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-148631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c31 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-75809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 269219/625000) (δ := 1041/100000000) (ψ := 176023/250000) 105 57
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t31 : ((-34050489759/1250000000000 : ℚ) : ℝ) ≤ stT105 31 := by
  have hc : ((-37917/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34050489759/1250000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-37917/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c32 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((84367/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533213/5000000) (δ := 53/5000000) (ψ := 176023/250000) 105 58
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t32 : ((149119017047/2500000000000 : ℚ) : ℝ) ≤ stT105 32 := by
  have hc : ((168709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((149119017047/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((168709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c33 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-420193/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1002227/2000000) (δ := 633/100000000) (ψ := 176023/250000) 105 58
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t33 : ((-731549348811/10000000000000 : ℚ) : ℝ) ≤ stT105 33 := by
  have hc : ((-420243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-731549348811/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-420243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c34 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((206901/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1430213/5000000) (δ := 829/100000000) (ψ := 176023/250000) 105 59
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t34 : ((17739461843/250000000000 : ℚ) : ℝ) ≤ stT105 34 := by
  have hc : ((51719/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17739461843/250000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((51719/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c35 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-80709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4748803/10000000) (δ := 317/50000000) (ψ := 176023/250000) 105 59
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t35 : ((-272888555887/5000000000000 : ℚ) : ℝ) ≤ stT105 35 := by
  have hc : ((-161443/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272888555887/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-161443/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c36 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((72283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -712861/2000000) (δ := 329/50000000) (ψ := 176023/250000) 105 60
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t36 : ((30107487957/1250000000000 : ℚ) : ℝ) ≤ stT105 36 := by
  have hc : ((36129/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30107487957/1250000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((36129/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c37 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((119341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145117/400000) (δ := 479/50000000) (ψ := 176023/250000) 105 60
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t37 : ((196113091799/10000000000000 : ℚ) : ℝ) ≤ stT105 37 := by
  have hc : ((119291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((196113091799/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((119291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c38 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-444891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5079623/10000000) (δ := 121/20000000) (ψ := 176023/250000) 105 61
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t38 : ((-144357992863/2000000000000 : ℚ) : ℝ) ≤ stT105 38 := by
  have hc : ((-444941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-144357992863/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-444941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c39 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((191921/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 869471/5000000) (δ := 299/50000000) (ψ := 176023/250000) 105 61
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t39 : ((614598869577/5000000000000 : ℚ) : ℝ) ≤ stT105 39 := by
  have hc : ((383817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614598869577/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((383817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c40 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-977537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -915387/1250000) (δ := 283/50000000) (ψ := 176023/250000) 105 62
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t40 : ((-1545700931593/10000000000000 : ℚ) : ℝ) ≤ stT105 40 := by
  have hc : ((-977587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1545700931593/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-977587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c41 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((943911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -420643/5000000) (δ := 333/50000000) (ψ := 176023/250000) 105 62
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t41 : ((1474062646557/10000000000000 : ℚ) : ℝ) ≤ stT105 41 := by
  have hc : ((943861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1474062646557/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((943861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c42 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-583419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2742161/5000000) (δ := 867/100000000) (ψ := 176023/250000) 105 62
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t42 : ((-450156252473/5000000000000 : ℚ) : ℝ) ≤ stT105 42 := by
  have hc : ((-583469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-450156252473/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-583469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c43 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-2397/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2023443/5000000) (δ := 453/50000000) (ψ := 176023/250000) 105 63
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t43 : ((-3659203907/500000000000 : ℚ) : ℝ) ≤ stT105 43 := by
  have hc : ((-4799/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3659203907/500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-4799/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c44 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((700181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1987863/10000000) (δ := 87/12500000) (ψ := 176023/250000) 105 63
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t44 : ((263871672459/2500000000000 : ℚ) : ℝ) ≤ stT105 44 := by
  have hc : ((700131/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((263871672459/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((700131/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c45 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-999913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488811/625000) (δ := 927/100000000) (ψ := 176023/250000) 105 64
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t45 : ((-186332105457/1250000000000 : ℚ) : ℝ) ≤ stT105 45 := by
  have hc : ((-999963/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186332105457/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-999963/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c46 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((681779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2051513/10000000) (δ := 997/100000000) (ψ := 176023/250000) 105 64
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t46 : ((1005154190451/10000000000000 : ℚ) : ℝ) ≤ stT105 46 := by
  have hc : ((681729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1005154190451/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((681729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c47 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((16607/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1796933/5000000) (δ := 523/50000000) (ψ := 176023/250000) 105 64
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t47 : ((96858669547/5000000000000 : ℚ) : ℝ) ≤ stT105 47 := by
  have hc : ((66403/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96858669547/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((66403/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c48 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-437209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3293789/5000000) (δ := 39/4000000) (ψ := 176023/250000) 105 65
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t48 : ((-19721658187/156250000000 : ℚ) : ℝ) ≤ stT105 48 := by
  have hc : ((-218617/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19721658187/156250000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-218617/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c49 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((445783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -235003/2000000) (δ := 499/50000000) (ψ := 176023/250000) 105 65
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t49 : ((318398475909/2500000000000 : ℚ) : ℝ) ≤ stT105 49 := by
  have hc : ((222879/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((318398475909/2500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((222879/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c50 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-16079/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1032049/2500000) (δ := 203/20000000) (ψ := 176023/250000) 105 65
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t50 : ((-11376644523/1000000000000 : ℚ) : ℝ) ≤ stT105 50 := by
  have hc : ((-16089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11376644523/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-16089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c51 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-415759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3190789/5000000) (δ := 93/12500000) (ψ := 176023/250000) 105 66
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t51 : ((-72776804413/625000000000 : ℚ) : ℝ) ≤ stT105 51 := by
  have hc : ((-51973/62500 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72776804413/625000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-51973/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c52 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((870917/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -128433/1000000) (δ := 437/50000000) (ψ := 176023/250000) 105 66
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t52 : ((4830699249/40000000000 : ℚ) : ℝ) ≤ stT105 52 := by
  have hc : ((870867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4830699249/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((870867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c53 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((5273/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3715821/10000000) (δ := 467/50000000) (ψ := 176023/250000) 105 66
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t53 : ((11581962639/1000000000000 : ℚ) : ℝ) ≤ stT105 53 := by
  have hc : ((42159/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11581962639/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((42159/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c54 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-953121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7085457/10000000) (δ := 573/100000000) (ψ := 176023/250000) 105 67
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t54 : ((-324275446397/2500000000000 : ℚ) : ℝ) ≤ stT105 54 := by
  have hc : ((-953171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-324275446397/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-953171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c55 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((615699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -283601/1250000) (δ := 89/10000000) (ψ := 176023/250000) 105 67
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t55 : ((830140495951/10000000000000 : ℚ) : ℝ) ≤ stT105 55 := by
  have hc : ((615649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((830140495951/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((615649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c56 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((553347/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2461049/10000000) (δ := 23/2500000) (ψ := 176023/250000) 105 67
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t56 : ((369687050441/5000000000000 : ℚ) : ℝ) ≤ stT105 56 := by
  have hc : ((553297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((369687050441/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((553297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c57 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-191143/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1776797/2500000) (δ := 17/2500000) (ψ := 176023/250000) 105 67
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t57 : ((-253188456549/2000000000000 : ℚ) : ℝ) ≤ stT105 57 := by
  have hc : ((-191153/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253188456549/2000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-191153/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c58 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-43367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2017721/5000000) (δ := 943/100000000) (ψ := 176023/250000) 105 68
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t58 : ((-11401868621/2000000000000 : ℚ) : ℝ) ≤ stT105 58 := by
  have hc : ((-43417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11401868621/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-43417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c59 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((983711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 225923/5000000) (δ := 623/100000000) (ψ := 176023/250000) 105 68
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t59 : ((1280617435629/10000000000000 : ℚ) : ℝ) ≤ stT105 59 := by
  have hc : ((983661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1280617435629/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((983661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c60 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-11437/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 972743/2000000) (δ := 1/156250) (ψ := 176023/250000) 105 68
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t60 : ((-47254806383/1000000000000 : ℚ) : ℝ) ≤ stT105 60 := by
  have hc : ((-183017/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47254806383/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-183017/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c61 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-857981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6505307/10000000) (δ := 641/100000000) (ψ := 176023/250000) 105 69
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t61 : ((-1098596293439/10000000000000 : ℚ) : ℝ) ≤ stT105 61 := by
  have hc : ((-858031/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1098596293439/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-858031/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c62 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((6257/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55923/250000) (δ := 871/100000000) (ψ := 176023/250000) 105 69
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t62 : ((15891522513/200000000000 : ℚ) : ℝ) ≤ stT105 62 := by
  have hc : ((12513/20000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15891522513/200000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((12513/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c63 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((707199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 196317/1000000) (δ := 391/50000000) (ψ := 176023/250000) 105 69
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t63 : ((890923589269/10000000000000 : ℚ) : ℝ) ≤ stT105 63 := by
  have hc : ((707149/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((890923589269/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((707149/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c64 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-763069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6097113/10000000) (δ := 841/100000000) (ψ := 176023/250000) 105 69
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t64 : ((-953899513119/10000000000000 : ℚ) : ℝ) ≤ stT105 64 := by
  have hc : ((-763119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-953899513119/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-763119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c65 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-601681/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5541001/10000000) (δ := 89/12500000) (ψ := 176023/250000) 105 70
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t65 : ((-186588960597/2500000000000 : ℚ) : ℝ) ≤ stT105 65 := by
  have hc : ((-601731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186588960597/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-601731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c66 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((51109/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1533289/10000000) (δ := 611/100000000) (ψ := 176023/250000) 105 70
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t66 : ((251627748079/2500000000000 : ℚ) : ℝ) ≤ stT105 66 := by
  have hc : ((408847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251627748079/2500000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((408847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c67 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((568873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2414153/10000000) (δ := 881/100000000) (ψ := 176023/250000) 105 70
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t67 : ((347463823081/5000000000000 : ℚ) : ℝ) ≤ stT105 67 := by
  have hc : ((568823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((347463823081/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((568823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c68 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-813677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6303113/10000000) (δ := 1031/100000000) (ψ := 176023/250000) 105 70
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t68 : ((-986789644633/10000000000000 : ℚ) : ℝ) ≤ stT105 68 := by
  have hc : ((-813727/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-986789644633/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-813727/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c69 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-611749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1114533/2000000) (δ := 1021/100000000) (ψ := 176023/250000) 105 71
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t69 : ((-736519732341/10000000000000 : ℚ) : ℝ) ≤ stT105 69 := by
  have hc : ((-611799/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-736519732341/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-611799/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c70 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((2353/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1795621/10000000) (δ := 611/100000000) (ψ := 176023/250000) 105 71
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t70 : ((22497477837/250000000000 : ℚ) : ℝ) ≤ stT105 70 := by
  have hc : ((75291/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22497477837/250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((75291/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c71 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((358559/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385569/2000000) (δ := 391/50000000) (ψ := 176023/250000) 105 71
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t71 : ((212750669527/2500000000000 : ℚ) : ℝ) ≤ stT105 71 := by
  have hc : ((179267/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((212750669527/2500000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((179267/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c72 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-620121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2799617/5000000) (δ := 861/100000000) (ψ := 176023/250000) 105 71
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t72 : ((-45679935347/625000000000 : ℚ) : ℝ) ≤ stT105 72 := by
  have hc : ((-620171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45679935347/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-620171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c73 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-854401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3243991/5000000) (δ := 31/5000000) (ψ := 176023/250000) 105 72
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t73 : ((-250014925953/2500000000000 : ℚ) : ℝ) ≤ stT105 73 := by
  have hc : ((-854451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-250014925953/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-854451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c74 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((1229/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2916499/10000000) (δ := 953/100000000) (ψ := 176023/250000) 105 72
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t74 : ((11428010937/250000000000 : ℚ) : ℝ) ≤ stT105 74 := by
  have hc : ((39323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11428010937/250000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((39323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c75 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((121333/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 151761/2500000) (δ := 93/10000000) (ψ := 176023/250000) 105 72
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t75 : ((5603839929/50000000000 : ℚ) : ℝ) ≤ stT105 75 := by
  have hc : ((485307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5603839929/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((485307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c76 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-62729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1020979/2500000) (δ := 13/2000000) (ψ := 176023/250000) 105 72
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t76 : ((-72012472541/10000000000000 : ℚ) : ℝ) ≤ stT105 76 := by
  have hc : ((-62779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72012472541/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-62779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c77 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-24771/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7515337/10000000) (δ := 43/5000000) (ψ := 176023/250000) 105 72
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t77 : ((-56461209467/500000000000 : ℚ) : ℝ) ≤ stT105 77 := by
  have hc : ((-99089/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56461209467/500000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-99089/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c78 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-344209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2402741/5000000) (δ := 789/100000000) (ψ := 176023/250000) 105 73
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t78 : ((-194898446001/5000000000000 : ℚ) : ℝ) ≤ stT105 78 := by
  have hc : ((-344259/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194898446001/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-344259/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c79 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((52121/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91343/625000) (δ := 529/100000000) (ψ := 176023/250000) 105 73
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t79 : ((469097149041/5000000000000 : ℚ) : ℝ) ≤ stT105 79 := by
  have hc : ((416943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((469097149041/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((416943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c80 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((741041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1840443/10000000) (δ := 689/100000000) (ψ := 176023/250000) 105 73
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t80 : ((828452390703/10000000000000 : ℚ) : ℝ) ≤ stT105 80 := by
  have hc : ((740991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((828452390703/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((740991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c81 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-452659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2550677/5000000) (δ := 277/50000000) (ψ := 176023/250000) 105 73
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t81 : ((-62876300301/1250000000000 : ℚ) : ℝ) ≤ stT105 81 := by
  have hc : ((-452709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62876300301/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-452709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c82 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-982509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -738571/1000000) (δ := 289/50000000) (ψ := 176023/250000) 105 74
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t82 : ((-271263906161/2500000000000 : ℚ) : ℝ) ≤ stT105 82 := by
  have hc : ((-982559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-271263906161/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-982559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c83 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-110519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4203853/10000000) (δ := 499/50000000) (ψ := 176023/250000) 105 74
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t83 : ((-121365288867/10000000000000 : ℚ) : ℝ) ≤ stT105 83 := by
  have hc : ((-110569/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-121365288867/10000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-110569/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c84 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((455717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1060103/10000000) (δ := 549/50000000) (ψ := 176023/250000) 105 74
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t84 : ((124300132147/1250000000000 : ℚ) : ℝ) ≤ stT105 84 := by
  have hc : ((113923/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124300132147/1250000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((113923/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c85 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((683261/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2046443/10000000) (δ := 119/20000000) (ψ := 176023/250000) 105 74
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t85 : ((185261544393/2500000000000 : ℚ) : ℝ) ≤ stT105 85 := by
  have hc : ((683211/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185261544393/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((683211/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c86 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-458107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5116653/10000000) (δ := 199/20000000) (ψ := 176023/250000) 105 74
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t86 : ((-61755440187/1250000000000 : ℚ) : ℝ) ≤ stT105 86 := by
  have hc : ((-458157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61755440187/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-458157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c87 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-992933/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3778297/5000000) (δ := 429/50000000) (ψ := 176023/250000) 105 75
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t87 : ((-1064589983079/10000000000000 : ℚ) : ℝ) ≤ stT105 87 := by
  have hc : ((-992983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1064589983079/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-992983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c88 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-9967/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2278281/5000000) (δ := 29/3125000) (ψ := 176023/250000) 105 75
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t88 : ((-2656748469/100000000000 : ℚ) : ℝ) ≤ stT105 88 := by
  have hc : ((-9969/40000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2656748469/100000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-9969/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c89 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((100547/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1590429/10000000) (δ := 139/20000000) (ψ := 176023/250000) 105 75
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t89 : ((426291573511/5000000000000 : ℚ) : ℝ) ≤ stT105 89 := by
  have hc : ((402163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((426291573511/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((402163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c90 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((429617/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1342563/10000000) (δ := 29/4000000) (ψ := 176023/250000) 105 75
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t90 : ((14150921577/156250000000 : ℚ) : ℝ) ≤ stT105 90 := by
  have hc : ((53699/62500 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14150921577/156250000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((53699/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c91 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-1009/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 848629/2000000) (δ := 221/20000000) (ψ := 176023/250000) 105 75
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t91 : ((-1058138879/80000000000 : ℚ) : ℝ) ≤ stT105 91 := by
  have hc : ((-5047/40000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1058138879/80000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-5047/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c92 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-478141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3556013/5000000) (δ := 159/20000000) (ψ := 176023/250000) 105 75
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t92 : ((-249261480559/2500000000000 : ℚ) : ℝ) ≤ stT105 92 := by
  have hc : ((-239083/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-249261480559/2500000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-239083/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c93 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-16717/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -719759/1250000) (δ := 239/25000000) (ψ := 176023/250000) 105 76
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t93 : ((-8668011387/125000000000 : ℚ) : ℝ) ≤ stT105 93 := by
  have hc : ((-66873/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8668011387/125000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-66873/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c94 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((190359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2950559/10000000) (δ := 413/50000000) (ψ := 176023/250000) 105 76
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t94 : ((98157242307/2500000000000 : ℚ) : ℝ) ≤ stT105 94 := by
  have hc : ((95167/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98157242307/2500000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((95167/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c95 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((997613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -34551/2000000) (δ := 117/12500000) (ψ := 176023/250000) 105 76
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t95 : ((511738845807/5000000000000 : ℚ) : ℝ) ≤ stT105 95 := by
  have hc : ((997563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((511738845807/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((997563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c96 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((514489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2575961/10000000) (δ := 463/50000000) (ψ := 176023/250000) 105 76
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t96 : ((26252336609/500000000000 : ℚ) : ℝ) ≤ stT105 96 := by
  have hc : ((514439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26252336609/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((514439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c97 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-520709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5296193/10000000) (δ := 403/50000000) (ψ := 176023/250000) 105 76
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t97 : ((-528751088373/10000000000000 : ℚ) : ℝ) ≤ stT105 97 := by
  have hc : ((-520759/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-528751088373/10000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-520759/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c98 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-124819/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7719439/10000000) (δ := 807/100000000) (ψ := 176023/250000) 105 77
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t98 : ((-504370403053/5000000000000 : ℚ) : ℝ) ≤ stT105 98 := by
  have hc : ((-499301/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504370403053/5000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-499301/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c99 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-54481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5054441/10000000) (δ := 527/100000000) (ψ := 176023/250000) 105 77
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t99 : ((-109523513531/2500000000000 : ℚ) : ℝ) ≤ stT105 99 := by
  have hc : ((-217949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109523513531/2500000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-217949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c100 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((56819/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -604057/2500000) (δ := 897/100000000) (ψ := 176023/250000) 105 77
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t100 : ((28406971593/500000000000 : ℚ) : ℝ) ≤ stT105 100 := by
  have hc : ((28407/50000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28406971593/500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((28407/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c101 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((996937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 97867/5000000) (δ := 219/25000000) (ψ := 176023/250000) 105 77
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t101 : ((991939449819/10000000000000 : ℚ) : ℝ) ≤ stT105 101 := by
  have hc : ((996887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((991939449819/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((996887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c102 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((221083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2781961/10000000) (δ := 473/50000000) (ψ := 176023/250000) 105 77
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t102 : ((109439957763/2500000000000 : ℚ) : ℝ) ≤ stT105 102 := by
  have hc : ((110529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).1
  have hw2 : ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((990147/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109439957763/2500000000000 : ℚ) : ℝ)
      = ((990147/10000000 : ℚ) : ℝ) * ((110529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c103 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-268293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5342957/10000000) (δ := 897/100000000) (ψ := 176023/250000) 105 77
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t103 : ((-13219088747/250000000000 : ℚ) : ℝ) ≤ stT105 103 := by
  have hc : ((-134159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13219088747/250000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-134159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c104 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-999949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3914377/5000000) (δ := 519/50000000) (ψ := 176023/250000) 105 78
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t104 : ((-980580019419/10000000000000 : ℚ) : ℝ) ≤ stT105 104 := by
  have hc : ((-999999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).2
  have h0 : (0:ℝ) ≤ ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-980580019419/10000000000000 : ℚ) : ℝ)
      = ((980581/10000000 : ℚ) : ℝ) * ((-999999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c105 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-527719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5316773/10000000) (δ := 33/6250000) (ψ := 176023/250000) 105 78
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t105 : ((-515050294869/10000000000000 : ℚ) : ℝ) ≤ stT105 105 := by
  have hc : ((-527769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-515050294869/10000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-527769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c106 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((106339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2828603/10000000) (δ := 489/50000000) (ψ := 176023/250000) 105 78
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t106 : ((41309333821/1000000000000 : ℚ) : ℝ) ≤ stT105 106 := by
  have hc : ((212653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41309333821/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((212653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c107 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((989431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -90949/2500000) (δ := 139/20000000) (ψ := 176023/250000) 105 78
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t107 : ((59779389401/625000000000 : ℚ) : ℝ) ≤ stT105 107 := by
  have hc : ((989381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59779389401/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((989381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c108 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((336983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1039041/5000000) (δ := 31/4000000) (ψ := 176023/250000) 105 78
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t108 : ((648475671/10000000000 : ℚ) : ℝ) ≤ stT105 108 := by
  have hc : ((168479/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((648475671/10000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((168479/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c109 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-22621/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2248727/5000000) (δ := 429/50000000) (ψ := 176023/250000) 105 78
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t109 : ((-10835896851/500000000000 : ℚ) : ℝ) ≤ stT105 109 := by
  have hc : ((-11313/50000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10835896851/500000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-11313/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c110 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-463643/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6894731/10000000) (δ := 43/6250000) (ψ := 176023/250000) 105 78
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t110 : ((-110522570571/1250000000000 : ℚ) : ℝ) ≤ stT105 110 := by
  have hc : ((-115917/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110522570571/1250000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-115917/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c111 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-843767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6437651/10000000) (δ := 213/20000000) (ψ := 176023/250000) 105 79
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t111 : ((-400457828043/5000000000000 : ℚ) : ℝ) ≤ stT105 111 := by
  have hc : ((-843817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400457828043/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-843817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c112 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-62513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32667/80000) (δ := 91/12500000) (ψ := 176023/250000) 105 79
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t112 : ((-3694783091/625000000000 : ℚ) : ℝ) ≤ stT105 112 := by
  have hc : ((-62563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).2
  have h0 : (0:ℝ) ≤ ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3694783091/625000000000 : ℚ) : ℝ)
      = ((59057/625000 : ℚ) : ℝ) * ((-62563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c113 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((152967/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -875013/5000000) (δ := 173/20000000) (ψ := 176023/250000) 105 79
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t113 : ((1798621363/25000000000 : ℚ) : ℝ) ≤ stT105 113 := by
  have hc : ((152957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1798621363/25000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((152957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c114 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((974771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 140691/2500000) (δ := 113/20000000) (ψ := 176023/250000) 105 79
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t114 : ((182581813557/2000000000000 : ℚ) : ℝ) ≤ stT105 114 := by
  have hc : ((974721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182581813557/2000000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((974721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c115 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((415647/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 571071/2000000) (δ := 31/4000000) (ψ := 176023/250000) 105 79
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t115 : ((48443233111/1250000000000 : ℚ) : ℝ) ≤ stT105 115 := by
  have hc : ((415597/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48443233111/1250000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((415597/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c116 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-462171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160253/312500) (δ := 459/50000000) (ψ := 176023/250000) 105 79
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t116 : ((-429161567417/10000000000000 : ℚ) : ℝ) ≤ stT105 116 := by
  have hc : ((-462221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-429161567417/10000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-462221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c117 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-982181/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7381329/10000000) (δ := 143/20000000) (ψ := 176023/250000) 105 79
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t117 : ((-908073541731/10000000000000 : ℚ) : ℝ) ≤ stT105 117 := by
  have hc : ((-982231/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-908073541731/10000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-982231/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c118 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-95237/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3046289/5000000) (δ := 407/50000000) (ψ := 176023/250000) 105 80
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t118 : ((-14028568779/200000000000 : ℚ) : ℝ) ≤ stT105 118 := by
  have hc : ((-380973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14028568779/200000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-380973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c119 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((3969/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31019/80000) (δ := 959/100000000) (ψ := 176023/250000) 105 80
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t119 : ((1814603691/1000000000000 : ℚ) : ℝ) ≤ stT105 119 := by
  have hc : ((3959/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1814603691/1000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((3959/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c120 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((391201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1680709/10000000) (δ := 151/25000000) (ψ := 176023/250000) 105 80
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t120 : ((4463660439/62500000000 : ℚ) : ℝ) ≤ stT105 120 := by
  have hc : ((48897/62500 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4463660439/62500000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((48897/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c121 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((980247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 248863/5000000) (δ := 151/25000000) (ψ := 176023/250000) 105 80
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t121 : ((89108729073/1000000000000 : ℚ) : ℝ) ≤ stT105 121 := by
  have hc : ((980197/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89108729073/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((980197/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c122 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((485997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 332279/1250000) (δ := 307/50000000) (ψ := 176023/250000) 105 80
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t122 : ((439955518079/10000000000000 : ℚ) : ℝ) ≤ stT105 122 := by
  have hc : ((485947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((439955518079/10000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((485947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c123 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-342563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4801101/10000000) (δ := 549/100000000) (ψ := 176023/250000) 105 80
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t123 : ((-30892386371/1000000000000 : ℚ) : ℝ) ≤ stT105 123 := by
  have hc : ((-342613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30892386371/1000000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-342613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c124 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-186397/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6926619/10000000) (δ := 669/100000000) (ψ := 176023/250000) 105 80
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t124 : ((-167398518989/2000000000000 : ℚ) : ℝ) ≤ stT105 124 := by
  have hc : ((-186407/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-167398518989/2000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-186407/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c125 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-27827/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6672899/10000000) (δ := 673/100000000) (ψ := 176023/250000) 105 81
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t125 : ((-99562581999/1250000000000 : ℚ) : ℝ) ≤ stT105 125 := by
  have hc : ((-445257/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99562581999/1250000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-445257/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c126 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-258729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -916251/2000000) (δ := 1013/100000000) (ψ := 176023/250000) 105 81
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t126 : ((-230538706509/10000000000000 : ℚ) : ℝ) ≤ stT105 126 := by
  have hc : ((-258779/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230538706509/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-258779/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c127 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((67279/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -501229/2000000) (δ := 89/10000000) (ψ := 176023/250000) 105 81
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t127 : ((59694878349/1250000000000 : ℚ) : ℝ) ≤ stT105 127 := by
  have hc : ((269091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59694878349/1250000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((269091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c128 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((246009/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -447311/10000000) (δ := 13/2000000) (ψ := 176023/250000) 105 81
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t128 : ((434864248819/5000000000000 : ℚ) : ℝ) ≤ stT105 128 := by
  have hc : ((491993/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((434864248819/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((491993/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c129 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((803169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1595501/10000000) (δ := 1023/100000000) (ψ := 176023/250000) 105 81
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t129 : ((14142122471/200000000000 : ℚ) : ℝ) ≤ stT105 129 := by
  have hc : ((803119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14142122471/200000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((803119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c130 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((3037/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1811269/5000000) (δ := 543/100000000) (ψ := 176023/250000) 105 81
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t130 : ((5325057647/500000000000 : ℚ) : ℝ) ≤ stT105 130 := by
  have hc : ((12143/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5325057647/500000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((12143/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c131 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-78873/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2817021/5000000) (δ := 833/100000000) (ψ := 176023/250000) 105 81
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t131 : ((-55133756097/1000000000000 : ℚ) : ℝ) ≤ stT105 131 := by
  have hc : ((-315517/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55133756097/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-315517/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c132 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-497999/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7630249/10000000) (δ := 853/100000000) (ψ := 176023/250000) 105 81
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t132 : ((-54184326417/625000000000 : ℚ) : ℝ) ≤ stT105 132 := by
  have hc : ((-62253/62500 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-54184326417/625000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-62253/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c133 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-762929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1524143/2500000) (δ := 763/100000000) (ψ := 176023/250000) 105 82
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t133 : ((-66158672069/1000000000000 : ℚ) : ℝ) ≤ stT105 133 := by
  have hc : ((-762979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).2
  have h0 : (0:ℝ) ≤ ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66158672069/1000000000000 : ℚ) : ℝ)
      = ((86711/1000000 : ℚ) : ℝ) * ((-762979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c134 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-81223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4130271/10000000) (δ := 1073/100000000) (ψ := 176023/250000) 105 82
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t134 : ((-70209225237/10000000000000 : ℚ) : ℝ) ≤ stT105 134 := by
  have hc : ((-81273/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70209225237/10000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-81273/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c135 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((643729/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2178589/10000000) (δ := 81/10000000) (ψ := 176023/250000) 105 82
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t135 : ((276995027749/5000000000000 : ℚ) : ℝ) ≤ stT105 135 := by
  have hc : ((643679/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).1
  have hw2 : ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((430331/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((276995027749/5000000000000 : ℚ) : ℝ)
      = ((430331/5000000 : ℚ) : ℝ) * ((643679/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c136 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((199069/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -241311/10000000) (δ := 11/1250000) (ψ := 176023/250000) 105 82
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t136 : ((42672875007/500000000000 : ℚ) : ℝ) ≤ stT105 136 := by
  have hc : ((199059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42672875007/500000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((199059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c137 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((97767/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67271/400000) (δ := 783/100000000) (ψ := 176023/250000) 105 82
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t137 : ((334090324351/5000000000000 : ℚ) : ℝ) ≤ stT105 137 := by
  have hc : ((391043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334090324351/5000000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((391043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c138 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((67021/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1795437/5000000) (δ := 11/1250000) (ψ := 176023/250000) 105 82
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t138 : ((1782210843/156250000000 : ℚ) : ℝ) ≤ stT105 138 := by
  have hc : ((16749/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1782210843/156250000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((16749/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c139 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-292013/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5486189/10000000) (δ := 723/100000000) (ψ := 176023/250000) 105 82
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t139 : ((-123851709591/2500000000000 : ℚ) : ℝ) ≤ stT105 139 := by
  have hc : ((-146019/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123851709591/2500000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-146019/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c140 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-981159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7367917/10000000) (δ := 853/100000000) (ψ := 176023/250000) 105 82
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t140 : ((-165854738479/2000000000000 : ℚ) : ℝ) ≤ stT105 140 := by
  have hc : ((-981209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165854738479/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-981209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c141 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-851001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6471711/10000000) (δ := 911/100000000) (ψ := 176023/250000) 105 83
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t141 : ((-89589287719/1250000000000 : ℚ) : ℝ) ≤ stT105 141 := by
  have hc : ((-851051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89589287719/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-851051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c142 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-272351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4616579/10000000) (δ := 591/100000000) (ψ := 176023/250000) 105 83
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t142 : ((-114297007991/5000000000000 : ℚ) : ℝ) ≤ stT105 142 := by
  have hc : ((-272401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114297007991/5000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-272401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c143 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((444853/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1387233/5000000) (δ := 371/50000000) (ψ := 176023/250000) 105 83
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t143 : ((185981475163/5000000000000 : ℚ) : ℝ) ≤ stT105 143 := by
  have hc : ((444803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185981475163/5000000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((444803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c144 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((29043/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -945191/10000000) (δ := 1011/100000000) (ψ := 176023/250000) 105 83
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t144 : ((387219011779/5000000000000 : ℚ) : ℝ) ≤ stT105 144 := by
  have hc : ((464663/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387219011779/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((464663/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c145 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((469931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 435713/5000000) (δ := 153/25000000) (ψ := 176023/250000) 105 83
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t145 : ((97558829331/1250000000000 : ℚ) : ℝ) ≤ stT105 145 := by
  have hc : ((234953/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97558829331/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((234953/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c146 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((479929/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 668889/2500000) (δ := 431/50000000) (ψ := 176023/250000) 105 83
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t146 : ((79430051959/2000000000000 : ℚ) : ℝ) ≤ stT105 146 := by
  have hc : ((479879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).1
  have hw2 : ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((165521/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79430051959/2000000000000 : ℚ) : ℝ)
      = ((165521/2000000 : ℚ) : ℝ) * ((479879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c147 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-214473/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1116843/2500000) (δ := 881/100000000) (ψ := 176023/250000) 105 83
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t147 : ((-176935781601/10000000000000 : ℚ) : ℝ) ≤ stT105 147 := by
  have hc : ((-214523/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176935781601/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-214523/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c148 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-400217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9761/15625) (δ := 751/100000000) (ψ := 176023/250000) 105 83
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t148 : ((-32899692279/500000000000 : ℚ) : ℝ) ≤ stT105 148 := by
  have hc : ((-200121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32899692279/500000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-200121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c149 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-498967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -192331/250000) (δ := 1021/100000000) (ψ := 176023/250000) 105 84
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t149 : ((-798418387/9765625000 : ℚ) : ℝ) ≤ stT105 149 := by
  have hc : ((-31187/31250 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).2
  have h0 : (0:ℝ) ≤ ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-798418387/9765625000 : ℚ) : ℝ)
      = ((25601/312500 : ℚ) : ℝ) * ((-31187/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c150 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-144049/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -296869/500000) (δ := 491/50000000) (ψ := 176023/250000) 105 84
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t150 : ((-117623741323/2000000000000 : ℚ) : ℝ) ≤ stT105 150 := by
  have hc : ((-144059/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117623741323/2000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-144059/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c151 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-53139/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1048297/2500000) (δ := 691/100000000) (ψ := 176023/250000) 105 84
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t151 : ((-10816069599/1250000000000 : ℚ) : ℝ) ≤ stT105 151 := by
  have hc : ((-13291/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10816069599/1250000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-13291/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c152 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((553527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -615127/2500000) (δ := 841/100000000) (ψ := 176023/250000) 105 84
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t152 : ((448929069039/10000000000000 : ℚ) : ℝ) ≤ stT105 152 := by
  have hc : ((553477/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448929069039/10000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((553477/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c153 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((191321/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -739191/10000000) (δ := 861/100000000) (ψ := 176023/250000) 105 84
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t153 : ((38666440143/500000000000 : ℚ) : ℝ) ≤ stT105 153 := by
  have hc : ((191311/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38666440143/500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((191311/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c154 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((925529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 970913/10000000) (δ := 1051/100000000) (ψ := 176023/250000) 105 84
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t154 : ((372885669369/5000000000000 : ℚ) : ℝ) ≤ stT105 154 := by
  have hc : ((925479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372885669369/5000000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((925479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c155 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((60237/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 667487/2500000) (δ := 901/100000000) (ψ := 176023/250000) 105 84
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t155 : ((193513931137/5000000000000 : ℚ) : ℝ) ≤ stT105 155 := by
  have hc : ((240923/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193513931137/5000000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((240923/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c156 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-171573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4358057/10000000) (δ := 991/100000000) (ψ := 176023/250000) 105 84
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t156 : ((-137408410343/10000000000000 : ℚ) : ℝ) ≤ stT105 156 := by
  have hc : ((-171623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137408410343/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-171623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c157 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-373439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6035379/10000000) (δ := 1011/100000000) (ψ := 176023/250000) 105 84
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t157 : ((-37257095421/625000000000 : ℚ) : ℝ) ≤ stT105 157 := by
  have hc : ((-46683/62500 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37257095421/625000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-46683/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c158 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-499077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7702051/10000000) (δ := 731/100000000) (ψ := 176023/250000) 105 84
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t158 : ((-99266147229/1250000000000 : ℚ) : ℝ) ≤ stT105 158 := by
  have hc : ((-249551/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99266147229/1250000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-249551/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c159 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-41219/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1269951/2000000) (δ := 13/1250000) (ψ := 176023/250000) 105 85
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t159 : ((-16345396509/250000000000 : ℚ) : ℝ) ≤ stT105 159 := by
  have hc : ((-82443/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16345396509/250000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-82443/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c160 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-305817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2351991/5000000) (δ := 23/2500000) (ψ := 176023/250000) 105 85
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t160 : ((-24180927419/1000000000000 : ℚ) : ℝ) ≤ stT105 160 := by
  have hc : ((-305867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24180927419/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-305867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c161 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((336701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1534231/5000000) (δ := 683/100000000) (ψ := 176023/250000) 105 85
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t161 : ((26531801961/1000000000000 : ℚ) : ℝ) ≤ stT105 161 := by
  have hc : ((336651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26531801961/1000000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((336651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c162 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((837979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -144307/1000000) (δ := 69/10000000) (ψ := 176023/250000) 105 85
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t162 : ((329169514573/5000000000000 : ℚ) : ℝ) ≤ stT105 162 := by
  have hc : ((837929/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((329169514573/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((837929/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c163 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((7981/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172319/10000000) (δ := 27/2500000) (ψ := 176023/250000) 105 85
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t163 : ((1562721189/20000000000 : ℚ) : ℝ) ≤ stT105 163 := by
  have hc : ((39903/40000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1562721189/20000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((39903/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c164 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((94703/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1777829/10000000) (δ := 39/5000000) (ψ := 176023/250000) 105 85
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t164 : ((73945661779/1250000000000 : ℚ) : ℝ) ≤ stT105 164 := by
  have hc : ((378787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73945661779/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((378787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c165 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((219561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3373579/10000000) (δ := 773/100000000) (ψ := 176023/250000) 105 85
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t165 : ((85444437239/5000000000000 : ℚ) : ℝ) ≤ stT105 165 := by
  have hc : ((219511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85444437239/5000000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((219511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c166 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-40143/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2479843/5000000) (δ := 903/100000000) (ψ := 176023/250000) 105 85
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t166 : ((-7790227587/250000000000 : ℚ) : ℝ) ≤ stT105 166 := by
  have hc : ((-10037/25000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7790227587/250000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-10037/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c167 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-864277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6536267/10000000) (δ := 3/312500) (ψ := 176023/250000) 105 85
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t167 : ((-10450577757/156250000000 : ℚ) : ℝ) ≤ stT105 167 := by
  have hc : ((-864327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10450577757/156250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-864327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c168 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-497513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7604527/10000000) (δ := 813/100000000) (ψ := 176023/250000) 105 86
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t168 : ((-191929512573/2500000000000 : ℚ) : ℝ) ≤ stT105 168 := by
  have hc : ((-248769/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-191929512573/2500000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-248769/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c169 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-749871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6046659/10000000) (δ := 23/2500000) (ψ := 176023/250000) 105 86
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t169 : ((-576862480751/10000000000000 : ℚ) : ℝ) ≤ stT105 169 := by
  have hc : ((-749921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-576862480751/10000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-749921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c170 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-14151/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2248991/5000000) (δ := 69/10000000) (ψ := 176023/250000) 105 86
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t170 : ((-17369149569/1000000000000 : ℚ) : ℝ) ≤ stT105 170 := by
  have hc : ((-113233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).2
  have h0 : (0:ℝ) ≤ ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-17369149569/1000000000000 : ℚ) : ℝ)
      = ((153393/2000000 : ℚ) : ℝ) * ((-113233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c171 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((18891/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -739597/2500000) (δ := 573/100000000) (ψ := 176023/250000) 105 86
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t171 : ((28888789663/1000000000000 : ℚ) : ℝ) ≤ stT105 171 := by
  have hc : ((37777/100000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28888789663/1000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((37777/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c172 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((420651/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1427771/10000000) (δ := 803/100000000) (ψ := 176023/250000) 105 86
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t172 : ((40090494999/625000000000 : ℚ) : ℝ) ≤ stT105 172 := by
  have hc : ((210313/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40090494999/625000000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((210313/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c173 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((499647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23493/2500000) (δ := 973/100000000) (ψ := 176023/250000) 105 86
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t173 : ((37985511227/500000000000 : ℚ) : ℝ) ≤ stT105 173 := by
  have hc : ((249811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).1
  have hw2 : ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((152057/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37985511227/500000000000 : ℚ) : ℝ)
      = ((152057/2000000 : ℚ) : ℝ) * ((249811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c174 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((400217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321389/2000000) (δ := 1043/100000000) (ψ := 176023/250000) 105 86
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t174 : ((2370193397/39062500000 : ℚ) : ℝ) ≤ stT105 174 := by
  have hc : ((12506/15625 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).1
  have hw2 : ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((379049/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2370193397/39062500000 : ℚ) : ℝ)
      = ((379049/5000000 : ℚ) : ℝ) * ((12506/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c175 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((160269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3111247/10000000) (δ := 773/100000000) (ψ := 176023/250000) 105 86
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t175 : ((3785403951/156250000000 : ℚ) : ℝ) ≤ stT105 175 := by
  have hc : ((40061/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3785403951/156250000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((40061/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c176 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-268653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4606977/10000000) (δ := 973/100000000) (ψ := 176023/250000) 105 86
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t176 : ((-202542678637/10000000000000 : ℚ) : ℝ) ≤ stT105 176 := by
  have hc : ((-268703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).2
  have h0 : (0:ℝ) ≤ ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202542678637/10000000000000 : ℚ) : ℝ)
      = ((753779/10000000 : ℚ) : ℝ) * ((-268703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c177 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-190581/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6094233/10000000) (δ := 37/5000000) (ψ := 176023/250000) 105 86
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t177 : ((-286518064989/5000000000000 : ℚ) : ℝ) ≤ stT105 177 := by
  have hc : ((-381187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286518064989/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-381187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c178 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-31053/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 757311/1000000) (δ := 7/1250000) (ψ := 176023/250000) 105 86
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t178 : ((-93105553359/1250000000000 : ℚ) : ℝ) ≤ stT105 178 := by
  have hc : ((-496873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-93105553359/1250000000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-496873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c179 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-444443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6664261/10000000) (δ := 1019/100000000) (ψ := 176023/250000) 105 87
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t179 : ((-20763211503/312500000000 : ℚ) : ℝ) ≤ stT105 179 := by
  have hc : ((-111117/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20763211503/312500000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-111117/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c180 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-122033/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5201861/10000000) (δ := 267/50000000) (ψ := 176023/250000) 105 87
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t180 : ((-45483672849/1250000000000 : ℚ) : ℝ) ≤ stT105 180 := by
  have hc : ((-244091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45483672849/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-244091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c181 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((71709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -936891/2500000) (δ := 739/100000000) (ψ := 176023/250000) 105 87
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t181 : ((26631852373/5000000000000 : ℚ) : ℝ) ≤ stT105 181 := by
  have hc : ((71659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26631852373/5000000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((71659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c182 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((605413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2301279/10000000) (δ := 457/50000000) (ψ := 176023/250000) 105 87
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t182 : ((448724718387/10000000000000 : ℚ) : ℝ) ≤ stT105 182 := by
  have hc : ((605363/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).1
  have hw2 : ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((741249/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((448724718387/10000000000000 : ℚ) : ℝ)
      = ((741249/10000000 : ℚ) : ℝ) * ((605363/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c183 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((941019/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21573/250000) (δ := 529/100000000) (ψ := 176023/250000) 105 87
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t183 : ((695584045149/10000000000000 : ℚ) : ℝ) ≤ stT105 183 := by
  have hc : ((940969/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((695584045149/10000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((940969/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c184 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((974337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 283801/5000000) (δ := 151/25000000) (ψ := 176023/250000) 105 87
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t184 : ((718253144983/10000000000000 : ℚ) : ℝ) ≤ stT105 184 := by
  have hc : ((974287/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718253144983/10000000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((974287/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c185 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((139893/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1990369/10000000) (δ := 819/100000000) (ψ := 176023/250000) 105 87
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t185 : ((51421969981/1000000000000 : ℚ) : ℝ) ≤ stT105 185 := by
  have hc : ((139883/200000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51421969981/1000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((139883/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c186 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((2071/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3405467/10000000) (δ := 377/50000000) (ψ := 176023/250000) 105 87
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t186 : ((607265227/40000000000 : ℚ) : ℝ) ≤ stT105 186 := by
  have hc : ((4141/20000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((607265227/40000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((4141/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c187 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-347023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4812977/10000000) (δ := 899/100000000) (ψ := 176023/250000) 105 87
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t187 : ((-253805113929/10000000000000 : ℚ) : ℝ) ≤ stT105 187 := by
  have hc : ((-347073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253805113929/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-347073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c188 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-396097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310649/500000) (δ := 39/6250000) (ψ := 176023/250000) 105 87
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t188 : ((-5778033553/100000000000 : ℚ) : ℝ) ≤ stT105 188 := by
  have hc : ((-198061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5778033553/100000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-198061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c189 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-995067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7605557/10000000) (δ := 899/100000000) (ψ := 176023/250000) 105 87
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t189 : ((-723841139981/10000000000000 : ℚ) : ℝ) ≤ stT105 189 := by
  have hc : ((-995117/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-723841139981/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-995117/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c190 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-56149/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6717179/10000000) (δ := 149/20000000) (ψ := 176023/250000) 105 88
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t190 : ((-325896601509/5000000000000 : ℚ) : ℝ) ≤ stT105 190 := by
  have hc : ((-449217/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-325896601509/5000000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-449217/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c191 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-21413/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5339223/10000000) (δ := 3/390625) (ψ := 176023/250000) 105 88
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t191 : ((-123962869/3200000000 : ℚ) : ℝ) ≤ stT105 191 := by
  have hc : ((-4283/8000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).2
  have h0 : (0:ℝ) ≤ ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123962869/3200000000 : ℚ) : ℝ)
      = ((28943/400000 : ℚ) : ℝ) * ((-4283/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c192 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-4147/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3968463/10000000) (δ := 147/20000000) (ψ := 176023/250000) 105 88
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t192 : ((-750465309/625000000000 : ℚ) : ℝ) ≤ stT105 192 := by
  have hc : ((-8319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).2
  have h0 : (0:ℝ) ≤ ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750465309/625000000000 : ℚ) : ℝ)
      = ((90211/1250000 : ℚ) : ℝ) * ((-8319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c193 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((126139/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2604823/10000000) (δ := 187/20000000) (ψ := 176023/250000) 105 88
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t193 : ((36315098639/1000000000000 : ℚ) : ℝ) ≤ stT105 193 := by
  have hc : ((252253/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36315098639/1000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((252253/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c194 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((438961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1248231/10000000) (δ := 123/20000000) (ψ := 176023/250000) 105 88
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t194 : ((19696100793/312500000000 : ℚ) : ℝ) ≤ stT105 194 := by
  have hc : ((54867/62500 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19696100793/312500000000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((54867/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c195 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((499589/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 50693/5000000) (δ := 119/20000000) (ψ := 176023/250000) 105 88
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t195 : ((44718096787/625000000000 : ℚ) : ℝ) ≤ stT105 195 := by
  have hc : ((124891/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44718096787/625000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((124891/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c196 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((418877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14441/100000) (δ := 121/20000000) (ψ := 176023/250000) 105 88
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t196 : ((14958985041/250000000000 : ℚ) : ℝ) ≤ stT105 196 := by
  have hc : ((104713/125000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14958985041/250000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((104713/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c197 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((110719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2779981/10000000) (δ := 379/50000000) (ψ := 176023/250000) 105 88
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t197 : ((15775012011/500000000000 : ℚ) : ℝ) ≤ stT105 197 := by
  have hc : ((221413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15775012011/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((221413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c198 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-36389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4109097/10000000) (δ := 3/390625) (ψ := 176023/250000) 105 88
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t198 : ((-1293916869/250000000000 : ℚ) : ℝ) ≤ stT105 198 := by
  have hc : ((-18207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1293916869/250000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-18207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c199 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-70767/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2715759/5000000) (δ := 207/25000000) (ψ := 176023/250000) 105 88
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t199 : ((-100339766013/2500000000000 : ℚ) : ℝ) ≤ stT105 199 := by
  have hc : ((-283093/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-100339766013/2500000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-283093/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_c200 :
    |Real.cos (((105 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((-225903/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6747311/10000000) (δ := 139/20000000) (ψ := 176023/250000) 105 88
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st105_t200 : ((-319492862917/5000000000000 : ℚ) : ℝ) ≤ stT105 200 := by
  have hc : ((-451831/500000 : ℚ) : ℝ)
      ≤ Real.cos (((105 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((176023/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st105_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-319492862917/5000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-451831/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st105_p1 : ((762149/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT105 (i+1) := by
  rw [Finset.sum_range_one]
  exact st105_t1

theorem st105_p2 : ((33232755177/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT105 (i+1))
      = (∑ i ∈ Finset.range 1, stT105 (i+1)) + stT105 2 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 1
    simpa using h
  have hprev := st105_p1
  have hstep := st105_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p3 : ((383951319903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT105 (i+1))
      = (∑ i ∈ Finset.range 2, stT105 (i+1)) + stT105 3 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 2
    simpa using h
  have hprev := st105_p2
  have hstep := st105_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p4 : ((2737736319903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT105 (i+1))
      = (∑ i ∈ Finset.range 3, stT105 (i+1)) + stT105 4 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 3
    simpa using h
  have hprev := st105_p3
  have hstep := st105_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p5 : ((801857810637/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT105 (i+1))
      = (∑ i ∈ Finset.range 4, stT105 (i+1)) + stT105 5 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 4
    simpa using h
  have hprev := st105_p4
  have hstep := st105_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p6 : ((4196483950483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT105 (i+1))
      = (∑ i ∈ Finset.range 5, stT105 (i+1)) + stT105 6 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 5
    simpa using h
  have hprev := st105_p5
  have hstep := st105_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p7 : ((5245925864261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT105 (i+1))
      = (∑ i ∈ Finset.range 6, stT105 (i+1)) + stT105 7 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 6
    simpa using h
  have hprev := st105_p6
  have hstep := st105_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p8 : ((23670905327/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT105 (i+1))
      = (∑ i ∈ Finset.range 7, stT105 (i+1)) + stT105 8 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 7
    simpa using h
  have hprev := st105_p7
  have hstep := st105_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p9 : ((342285975893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT105 (i+1))
      = (∑ i ∈ Finset.range 8, stT105 (i+1)) + stT105 9 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 8
    simpa using h
  have hprev := st105_p8
  have hstep := st105_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p10 : ((-355927469433/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT105 (i+1))
      = (∑ i ∈ Finset.range 9, stT105 (i+1)) + stT105 10 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 9
    simpa using h
  have hprev := st105_p9
  have hstep := st105_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p11 : ((284929669767/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT105 (i+1))
      = (∑ i ∈ Finset.range 10, stT105 (i+1)) + stT105 11 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 10
    simpa using h
  have hprev := st105_p10
  have hstep := st105_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p12 : ((-333702005521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT105 (i+1))
      = (∑ i ∈ Finset.range 11, stT105 (i+1)) + stT105 12 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 11
    simpa using h
  have hprev := st105_p11
  have hstep := st105_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p13 : ((-327206468521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT105 (i+1))
      = (∑ i ∈ Finset.range 12, stT105 (i+1)) + stT105 13 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 12
    simpa using h
  have hprev := st105_p12
  have hstep := st105_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p14 : ((67915630827/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT105 (i+1))
      = (∑ i ∈ Finset.range 13, stT105 (i+1)) + stT105 14 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 13
    simpa using h
  have hprev := st105_p13
  have hstep := st105_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p15 : ((370942402441/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT105 (i+1))
      = (∑ i ∈ Finset.range 14, stT105 (i+1)) + stT105 15 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 14
    simpa using h
  have hprev := st105_p14
  have hstep := st105_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p16 : ((426749589941/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT105 (i+1))
      = (∑ i ∈ Finset.range 15, stT105 (i+1)) + stT105 16 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 15
    simpa using h
  have hprev := st105_p15
  have hstep := st105_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p17 : ((57019401553/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT105 (i+1))
      = (∑ i ∈ Finset.range 16, stT105 (i+1)) + stT105 17 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 16
    simpa using h
  have hprev := st105_p16
  have hstep := st105_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p18 : ((565081448621/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT105 (i+1))
      = (∑ i ∈ Finset.range 17, stT105 (i+1)) + stT105 18 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 17
    simpa using h
  have hprev := st105_p17
  have hstep := st105_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p19 : ((6432035375989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT105 (i+1))
      = (∑ i ∈ Finset.range 18, stT105 (i+1)) + stT105 19 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 18
    simpa using h
  have hprev := st105_p18
  have hstep := st105_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p20 : ((8560399972867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT105 (i+1))
      = (∑ i ∈ Finset.range 19, stT105 (i+1)) + stT105 20 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 19
    simpa using h
  have hprev := st105_p19
  have hstep := st105_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p21 : ((8776210830533/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT105 (i+1))
      = (∑ i ∈ Finset.range 20, stT105 (i+1)) + stT105 21 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 20
    simpa using h
  have hprev := st105_p20
  have hstep := st105_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p22 : ((6722091478797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT105 (i+1))
      = (∑ i ∈ Finset.range 21, stT105 (i+1)) + stT105 22 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 21
    simpa using h
  have hprev := st105_p21
  have hstep := st105_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p23 : ((6253997277747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT105 (i+1))
      = (∑ i ∈ Finset.range 22, stT105 (i+1)) + stT105 23 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 22
    simpa using h
  have hprev := st105_p22
  have hstep := st105_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p24 : ((2073708017697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT105 (i+1))
      = (∑ i ∈ Finset.range 23, stT105 (i+1)) + stT105 24 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 23
    simpa using h
  have hprev := st105_p23
  have hstep := st105_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p25 : ((3718405820889/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT105 (i+1))
      = (∑ i ∈ Finset.range 24, stT105 (i+1)) + stT105 25 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 24
    simpa using h
  have hprev := st105_p24
  have hstep := st105_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p26 : ((804975248463/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT105 (i+1))
      = (∑ i ∈ Finset.range 25, stT105 (i+1)) + stT105 26 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 25
    simpa using h
  have hprev := st105_p25
  have hstep := st105_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p27 : ((1039914359463/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT105 (i+1))
      = (∑ i ∈ Finset.range 26, stT105 (i+1)) + stT105 27 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 26
    simpa using h
  have hprev := st105_p26
  have hstep := st105_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p28 : ((6626341508853/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT105 (i+1))
      = (∑ i ∈ Finset.range 27, stT105 (i+1)) + stT105 28 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 27
    simpa using h
  have hprev := st105_p27
  have hstep := st105_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p29 : ((7623944941231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT105 (i+1))
      = (∑ i ∈ Finset.range 28, stT105 (i+1)) + stT105 29 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 28
    simpa using h
  have hprev := st105_p28
  have hstep := st105_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p30 : ((7352583082029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT105 (i+1))
      = (∑ i ∈ Finset.range 29, stT105 (i+1)) + stT105 30 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 29
    simpa using h
  have hprev := st105_p29
  have hstep := st105_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p31 : ((7080179163957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT105 (i+1))
      = (∑ i ∈ Finset.range 30, stT105 (i+1)) + stT105 31 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 30
    simpa using h
  have hprev := st105_p30
  have hstep := st105_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p32 : ((1535331046429/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT105 (i+1))
      = (∑ i ∈ Finset.range 31, stT105 (i+1)) + stT105 32 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 31
    simpa using h
  have hprev := st105_p31
  have hstep := st105_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p33 : ((3472552941667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT105 (i+1))
      = (∑ i ∈ Finset.range 32, stT105 (i+1)) + stT105 33 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 32
    simpa using h
  have hprev := st105_p32
  have hstep := st105_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p34 : ((3827342178527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT105 (i+1))
      = (∑ i ∈ Finset.range 33, stT105 (i+1)) + stT105 34 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 33
    simpa using h
  have hprev := st105_p33
  have hstep := st105_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p35 : ((44430670283/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT105 (i+1))
      = (∑ i ∈ Finset.range 34, stT105 (i+1)) + stT105 35 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 34
    simpa using h
  have hprev := st105_p34
  have hstep := st105_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p36 : ((918720893617/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT105 (i+1))
      = (∑ i ∈ Finset.range 35, stT105 (i+1)) + stT105 36 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 35
    simpa using h
  have hprev := st105_p35
  have hstep := st105_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p37 : ((1509176048147/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT105 (i+1))
      = (∑ i ∈ Finset.range 36, stT105 (i+1)) + stT105 37 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 36
    simpa using h
  have hprev := st105_p36
  have hstep := st105_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p38 : ((341204513821/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT105 (i+1))
      = (∑ i ∈ Finset.range 37, stT105 (i+1)) + stT105 38 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 37
    simpa using h
  have hprev := st105_p37
  have hstep := st105_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p39 : ((4026644007787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT105 (i+1))
      = (∑ i ∈ Finset.range 38, stT105 (i+1)) + stT105 39 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 38
    simpa using h
  have hprev := st105_p38
  have hstep := st105_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p40 : ((6507587083981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT105 (i+1))
      = (∑ i ∈ Finset.range 39, stT105 (i+1)) + stT105 40 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 39
    simpa using h
  have hprev := st105_p39
  have hstep := st105_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p41 : ((3990824865269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT105 (i+1))
      = (∑ i ∈ Finset.range 40, stT105 (i+1)) + stT105 41 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 40
    simpa using h
  have hprev := st105_p40
  have hstep := st105_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p42 : ((885167153199/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT105 (i+1))
      = (∑ i ∈ Finset.range 41, stT105 (i+1)) + stT105 42 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 41
    simpa using h
  have hprev := st105_p41
  have hstep := st105_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p43 : ((1752038286863/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT105 (i+1))
      = (∑ i ∈ Finset.range 42, stT105 (i+1)) + stT105 43 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 42
    simpa using h
  have hprev := st105_p42
  have hstep := st105_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p44 : ((1007954979661/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT105 (i+1))
      = (∑ i ∈ Finset.range 43, stT105 (i+1)) + stT105 44 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 43
    simpa using h
  have hprev := st105_p43
  have hstep := st105_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p45 : ((205405718551/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT105 (i+1))
      = (∑ i ∈ Finset.range 44, stT105 (i+1)) + stT105 45 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 44
    simpa using h
  have hprev := st105_p44
  have hstep := st105_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p46 : ((7578137184083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT105 (i+1))
      = (∑ i ∈ Finset.range 45, stT105 (i+1)) + stT105 46 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 45
    simpa using h
  have hprev := st105_p45
  have hstep := st105_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p47 : ((7771854523177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT105 (i+1))
      = (∑ i ∈ Finset.range 46, stT105 (i+1)) + stT105 47 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 46
    simpa using h
  have hprev := st105_p46
  have hstep := st105_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p48 : ((6509668399209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT105 (i+1))
      = (∑ i ∈ Finset.range 47, stT105 (i+1)) + stT105 48 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 47
    simpa using h
  have hprev := st105_p47
  have hstep := st105_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p49 : ((1556652460569/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT105 (i+1))
      = (∑ i ∈ Finset.range 48, stT105 (i+1)) + stT105 49 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 48
    simpa using h
  have hprev := st105_p48
  have hstep := st105_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p50 : ((1533899171523/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT105 (i+1))
      = (∑ i ∈ Finset.range 49, stT105 (i+1)) + stT105 50 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 49
    simpa using h
  have hprev := st105_p49
  have hstep := st105_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p51 : ((6505066987007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT105 (i+1))
      = (∑ i ∈ Finset.range 50, stT105 (i+1)) + stT105 51 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 50
    simpa using h
  have hprev := st105_p50
  have hstep := st105_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p52 : ((7712741799257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT105 (i+1))
      = (∑ i ∈ Finset.range 51, stT105 (i+1)) + stT105 52 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 51
    simpa using h
  have hprev := st105_p51
  have hstep := st105_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p53 : ((7828561425647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT105 (i+1))
      = (∑ i ∈ Finset.range 52, stT105 (i+1)) + stT105 53 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 52
    simpa using h
  have hprev := st105_p52
  have hstep := st105_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p54 : ((6531459640059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT105 (i+1))
      = (∑ i ∈ Finset.range 53, stT105 (i+1)) + stT105 54 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 53
    simpa using h
  have hprev := st105_p53
  have hstep := st105_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p55 : ((736160013601/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT105 (i+1))
      = (∑ i ∈ Finset.range 54, stT105 (i+1)) + stT105 55 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 54
    simpa using h
  have hprev := st105_p54
  have hstep := st105_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p56 : ((2025243559223/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT105 (i+1))
      = (∑ i ∈ Finset.range 55, stT105 (i+1)) + stT105 56 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 55
    simpa using h
  have hprev := st105_p55
  have hstep := st105_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p57 : ((6835031954147/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT105 (i+1))
      = (∑ i ∈ Finset.range 56, stT105 (i+1)) + stT105 57 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 56
    simpa using h
  have hprev := st105_p56
  have hstep := st105_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p58 : ((3389011305521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT105 (i+1))
      = (∑ i ∈ Finset.range 57, stT105 (i+1)) + stT105 58 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 57
    simpa using h
  have hprev := st105_p57
  have hstep := st105_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p59 : ((8058640046671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT105 (i+1))
      = (∑ i ∈ Finset.range 58, stT105 (i+1)) + stT105 59 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 58
    simpa using h
  have hprev := st105_p58
  have hstep := st105_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p60 : ((7586091982841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT105 (i+1))
      = (∑ i ∈ Finset.range 59, stT105 (i+1)) + stT105 60 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 59
    simpa using h
  have hprev := st105_p59
  have hstep := st105_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p61 : ((3243747844701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT105 (i+1))
      = (∑ i ∈ Finset.range 60, stT105 (i+1)) + stT105 61 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 60
    simpa using h
  have hprev := st105_p60
  have hstep := st105_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p62 : ((1820517953763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT105 (i+1))
      = (∑ i ∈ Finset.range 61, stT105 (i+1)) + stT105 62 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 61
    simpa using h
  have hprev := st105_p61
  have hstep := st105_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p63 : ((8172995404321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT105 (i+1))
      = (∑ i ∈ Finset.range 62, stT105 (i+1)) + stT105 63 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 62
    simpa using h
  have hprev := st105_p62
  have hstep := st105_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p64 : ((3609547945601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT105 (i+1))
      = (∑ i ∈ Finset.range 63, stT105 (i+1)) + stT105 64 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 63
    simpa using h
  have hprev := st105_p63
  have hstep := st105_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p65 : ((3236370024407/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT105 (i+1))
      = (∑ i ∈ Finset.range 64, stT105 (i+1)) + stT105 65 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 64
    simpa using h
  have hprev := st105_p64
  have hstep := st105_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p66 : ((747925104113/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT105 (i+1))
      = (∑ i ∈ Finset.range 65, stT105 (i+1)) + stT105 66 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 65
    simpa using h
  have hprev := st105_p65
  have hstep := st105_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p67 : ((2043544671823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT105 (i+1))
      = (∑ i ∈ Finset.range 66, stT105 (i+1)) + stT105 67 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 66
    simpa using h
  have hprev := st105_p66
  have hstep := st105_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p68 : ((7187389042659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT105 (i+1))
      = (∑ i ∈ Finset.range 67, stT105 (i+1)) + stT105 68 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 67
    simpa using h
  have hprev := st105_p67
  have hstep := st105_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p69 : ((3225434655159/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT105 (i+1))
      = (∑ i ∈ Finset.range 68, stT105 (i+1)) + stT105 69 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 68
    simpa using h
  have hprev := st105_p68
  have hstep := st105_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p70 : ((3675384211899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT105 (i+1))
      = (∑ i ∈ Finset.range 69, stT105 (i+1)) + stT105 70 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 69
    simpa using h
  have hprev := st105_p69
  have hstep := st105_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p71 : ((4100885550953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT105 (i+1))
      = (∑ i ∈ Finset.range 70, stT105 (i+1)) + stT105 71 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 70
    simpa using h
  have hprev := st105_p70
  have hstep := st105_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p72 : ((3735446068177/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT105 (i+1))
      = (∑ i ∈ Finset.range 71, stT105 (i+1)) + stT105 72 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 71
    simpa using h
  have hprev := st105_p71
  have hstep := st105_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p73 : ((3235416216271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT105 (i+1))
      = (∑ i ∈ Finset.range 72, stT105 (i+1)) + stT105 73 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 72
    simpa using h
  have hprev := st105_p72
  have hstep := st105_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p74 : ((3463976435011/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT105 (i+1))
      = (∑ i ∈ Finset.range 73, stT105 (i+1)) + stT105 74 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 73
    simpa using h
  have hprev := st105_p73
  have hstep := st105_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p75 : ((4024360427911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT105 (i+1))
      = (∑ i ∈ Finset.range 74, stT105 (i+1)) + stT105 75 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 74
    simpa using h
  have hprev := st105_p74
  have hstep := st105_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p76 : ((7976708383281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT105 (i+1))
      = (∑ i ∈ Finset.range 75, stT105 (i+1)) + stT105 76 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 75
    simpa using h
  have hprev := st105_p75
  have hstep := st105_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p77 : ((6847484193941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT105 (i+1))
      = (∑ i ∈ Finset.range 76, stT105 (i+1)) + stT105 77 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 76
    simpa using h
  have hprev := st105_p76
  have hstep := st105_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p78 : ((6457687301939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT105 (i+1))
      = (∑ i ∈ Finset.range 77, stT105 (i+1)) + stT105 78 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 77
    simpa using h
  have hprev := st105_p77
  have hstep := st105_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p79 : ((7395881600021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT105 (i+1))
      = (∑ i ∈ Finset.range 78, stT105 (i+1)) + stT105 79 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 78
    simpa using h
  have hprev := st105_p78
  have hstep := st105_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p80 : ((2056083497681/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT105 (i+1))
      = (∑ i ∈ Finset.range 79, stT105 (i+1)) + stT105 80 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 79
    simpa using h
  have hprev := st105_p79
  have hstep := st105_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p81 : ((1930330897079/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT105 (i+1))
      = (∑ i ∈ Finset.range 80, stT105 (i+1)) + stT105 81 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 80
    simpa using h
  have hprev := st105_p80
  have hstep := st105_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p82 : ((829533495459/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT105 (i+1))
      = (∑ i ∈ Finset.range 81, stT105 (i+1)) + stT105 82 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 81
    simpa using h
  have hprev := st105_p81
  have hstep := st105_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p83 : ((1302980534961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT105 (i+1))
      = (∑ i ∈ Finset.range 82, stT105 (i+1)) + stT105 83 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 82
    simpa using h
  have hprev := st105_p82
  have hstep := st105_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p84 : ((7509303731981/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT105 (i+1))
      = (∑ i ∈ Finset.range 83, stT105 (i+1)) + stT105 84 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 83
    simpa using h
  have hprev := st105_p83
  have hstep := st105_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p85 : ((8250349909553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT105 (i+1))
      = (∑ i ∈ Finset.range 84, stT105 (i+1)) + stT105 85 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 84
    simpa using h
  have hprev := st105_p84
  have hstep := st105_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p86 : ((7756306388057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT105 (i+1))
      = (∑ i ∈ Finset.range 85, stT105 (i+1)) + stT105 86 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 85
    simpa using h
  have hprev := st105_p85
  have hstep := st105_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p87 : ((3345858202489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT105 (i+1))
      = (∑ i ∈ Finset.range 86, stT105 (i+1)) + stT105 87 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 86
    simpa using h
  have hprev := st105_p86
  have hstep := st105_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p88 : ((3213020779039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT105 (i+1))
      = (∑ i ∈ Finset.range 87, stT105 (i+1)) + stT105 88 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 87
    simpa using h
  have hprev := st105_p87
  have hstep := st105_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p89 : ((72786247051/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT105 (i+1))
      = (∑ i ∈ Finset.range 88, stT105 (i+1)) + stT105 89 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 88
    simpa using h
  have hprev := st105_p88
  have hstep := st105_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p90 : ((2046070921507/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT105 (i+1))
      = (∑ i ∈ Finset.range 89, stT105 (i+1)) + stT105 90 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 89
    simpa using h
  have hprev := st105_p89
  have hstep := st105_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p91 : ((8052016326153/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT105 (i+1))
      = (∑ i ∈ Finset.range 90, stT105 (i+1)) + stT105 91 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 90
    simpa using h
  have hprev := st105_p90
  have hstep := st105_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p92 : ((7054970403917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT105 (i+1))
      = (∑ i ∈ Finset.range 91, stT105 (i+1)) + stT105 92 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 91
    simpa using h
  have hprev := st105_p91
  have hstep := st105_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p93 : ((6361529492957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT105 (i+1))
      = (∑ i ∈ Finset.range 92, stT105 (i+1)) + stT105 93 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 92
    simpa using h
  have hprev := st105_p92
  have hstep := st105_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p94 : ((1350831692437/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT105 (i+1))
      = (∑ i ∈ Finset.range 93, stT105 (i+1)) + stT105 94 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 93
    simpa using h
  have hprev := st105_p93
  have hstep := st105_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p95 : ((7777636153799/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT105 (i+1))
      = (∑ i ∈ Finset.range 94, stT105 (i+1)) + stT105 95 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 94
    simpa using h
  have hprev := st105_p94
  have hstep := st105_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p96 : ((8302682885979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT105 (i+1))
      = (∑ i ∈ Finset.range 95, stT105 (i+1)) + stT105 96 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 95
    simpa using h
  have hprev := st105_p95
  have hstep := st105_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p97 : ((3886965898803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT105 (i+1))
      = (∑ i ∈ Finset.range 96, stT105 (i+1)) + stT105 97 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 96
    simpa using h
  have hprev := st105_p96
  have hstep := st105_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p98 : ((13530381983/20000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT105 (i+1))
      = (∑ i ∈ Finset.range 97, stT105 (i+1)) + stT105 98 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 97
    simpa using h
  have hprev := st105_p97
  have hstep := st105_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p99 : ((197721779293/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT105 (i+1))
      = (∑ i ∈ Finset.range 98, stT105 (i+1)) + stT105 99 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 98
    simpa using h
  have hprev := st105_p98
  have hstep := st105_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p100 : ((1723809092309/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT105 (i+1))
      = (∑ i ∈ Finset.range 99, stT105 (i+1)) + stT105 100 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 99
    simpa using h
  have hprev := st105_p99
  have hstep := st105_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p101 : ((1577435163811/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT105 (i+1))
      = (∑ i ∈ Finset.range 100, stT105 (i+1)) + stT105 101 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 100
    simpa using h
  have hprev := st105_p100
  have hstep := st105_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p102 : ((8324935650107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT105 (i+1))
      = (∑ i ∈ Finset.range 101, stT105 (i+1)) + stT105 102 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 101
    simpa using h
  have hprev := st105_p101
  have hstep := st105_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p103 : ((7796172100227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT105 (i+1))
      = (∑ i ∈ Finset.range 102, stT105 (i+1)) + stT105 103 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 102
    simpa using h
  have hprev := st105_p102
  have hstep := st105_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p104 : ((851949010101/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT105 (i+1))
      = (∑ i ∈ Finset.range 103, stT105 (i+1)) + stT105 104 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 103
    simpa using h
  have hprev := st105_p103
  have hstep := st105_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p105 : ((6300541785939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT105 (i+1))
      = (∑ i ∈ Finset.range 104, stT105 (i+1)) + stT105 105 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 104
    simpa using h
  have hprev := st105_p104
  have hstep := st105_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p106 : ((6713635124149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT105 (i+1))
      = (∑ i ∈ Finset.range 105, stT105 (i+1)) + stT105 106 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 105
    simpa using h
  have hprev := st105_p105
  have hstep := st105_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p107 : ((1534021070913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT105 (i+1))
      = (∑ i ∈ Finset.range 106, stT105 (i+1)) + stT105 107 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 106
    simpa using h
  have hprev := st105_p106
  have hstep := st105_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p108 : ((1663716205113/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT105 (i+1))
      = (∑ i ∈ Finset.range 107, stT105 (i+1)) + stT105 108 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 107
    simpa using h
  have hprev := st105_p107
  have hstep := st105_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p109 : ((1620372617709/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT105 (i+1))
      = (∑ i ∈ Finset.range 108, stT105 (i+1)) + stT105 109 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 108
    simpa using h
  have hprev := st105_p108
  have hstep := st105_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p110 : ((7217682523977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT105 (i+1))
      = (∑ i ∈ Finset.range 109, stT105 (i+1)) + stT105 110 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 109
    simpa using h
  have hprev := st105_p109
  have hstep := st105_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p111 : ((6416766867891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT105 (i+1))
      = (∑ i ∈ Finset.range 110, stT105 (i+1)) + stT105 111 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 110
    simpa using h
  have hprev := st105_p110
  have hstep := st105_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p112 : ((1271530067687/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT105 (i+1))
      = (∑ i ∈ Finset.range 111, stT105 (i+1)) + stT105 112 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 111
    simpa using h
  have hprev := st105_p111
  have hstep := st105_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p113 : ((1415419776727/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT105 (i+1))
      = (∑ i ∈ Finset.range 112, stT105 (i+1)) + stT105 113 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 112
    simpa using h
  have hprev := st105_p112
  have hstep := st105_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p114 : ((399500397571/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT105 (i+1))
      = (∑ i ∈ Finset.range 113, stT105 (i+1)) + stT105 114 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 113
    simpa using h
  have hprev := st105_p113
  have hstep := st105_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p115 : ((2094388454077/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT105 (i+1))
      = (∑ i ∈ Finset.range 114, stT105 (i+1)) + stT105 115 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 114
    simpa using h
  have hprev := st105_p114
  have hstep := st105_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p116 : ((7948392248891/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT105 (i+1))
      = (∑ i ∈ Finset.range 115, stT105 (i+1)) + stT105 116 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 115
    simpa using h
  have hprev := st105_p115
  have hstep := st105_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p117 : ((176007967679/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT105 (i+1))
      = (∑ i ∈ Finset.range 116, stT105 (i+1)) + stT105 117 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 116
    simpa using h
  have hprev := st105_p116
  have hstep := st105_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p118 : ((633889026821/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT105 (i+1))
      = (∑ i ∈ Finset.range 117, stT105 (i+1)) + stT105 118 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 117
    simpa using h
  have hprev := st105_p117
  have hstep := st105_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p119 : ((39731476907/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT105 (i+1))
      = (∑ i ∈ Finset.range 118, stT105 (i+1)) + stT105 119 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 118
    simpa using h
  have hprev := st105_p118
  have hstep := st105_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p120 : ((22097568673/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT105 (i+1))
      = (∑ i ∈ Finset.range 119, stT105 (i+1)) + stT105 120 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 119
    simpa using h
  have hprev := st105_p119
  have hstep := st105_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p121 : ((796230926609/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT105 (i+1))
      = (∑ i ∈ Finset.range 120, stT105 (i+1)) + stT105 121 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 120
    simpa using h
  have hprev := st105_p120
  have hstep := st105_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p122 : ((8402264784169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT105 (i+1))
      = (∑ i ∈ Finset.range 121, stT105 (i+1)) + stT105 122 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 121
    simpa using h
  have hprev := st105_p121
  have hstep := st105_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p123 : ((8093340920459/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT105 (i+1))
      = (∑ i ∈ Finset.range 122, stT105 (i+1)) + stT105 123 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 122
    simpa using h
  have hprev := st105_p122
  have hstep := st105_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p124 : ((3628174162757/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT105 (i+1))
      = (∑ i ∈ Finset.range 123, stT105 (i+1)) + stT105 124 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 123
    simpa using h
  have hprev := st105_p123
  have hstep := st105_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p125 : ((3229923834761/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT105 (i+1))
      = (∑ i ∈ Finset.range 124, stT105 (i+1)) + stT105 125 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 124
    simpa using h
  have hprev := st105_p124
  have hstep := st105_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p126 : ((6229308963013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT105 (i+1))
      = (∑ i ∈ Finset.range 125, stT105 (i+1)) + stT105 126 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 125
    simpa using h
  have hprev := st105_p125
  have hstep := st105_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p127 : ((1341373597961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT105 (i+1))
      = (∑ i ∈ Finset.range 126, stT105 (i+1)) + stT105 127 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 126
    simpa using h
  have hprev := st105_p126
  have hstep := st105_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p128 : ((7576596487443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT105 (i+1))
      = (∑ i ∈ Finset.range 127, stT105 (i+1)) + stT105 128 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 127
    simpa using h
  have hprev := st105_p127
  have hstep := st105_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p129 : ((8283702610993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT105 (i+1))
      = (∑ i ∈ Finset.range 128, stT105 (i+1)) + stT105 129 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 128
    simpa using h
  have hprev := st105_p128
  have hstep := st105_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p130 : ((8390203763933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT105 (i+1))
      = (∑ i ∈ Finset.range 129, stT105 (i+1)) + stT105 130 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 129
    simpa using h
  have hprev := st105_p129
  have hstep := st105_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p131 : ((7838866202963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT105 (i+1))
      = (∑ i ∈ Finset.range 130, stT105 (i+1)) + stT105 131 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 130
    simpa using h
  have hprev := st105_p130
  have hstep := st105_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p132 : ((6971916980291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT105 (i+1))
      = (∑ i ∈ Finset.range 131, stT105 (i+1)) + stT105 132 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 131
    simpa using h
  have hprev := st105_p131
  have hstep := st105_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p133 : ((6310330259601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT105 (i+1))
      = (∑ i ∈ Finset.range 132, stT105 (i+1)) + stT105 133 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 132
    simpa using h
  have hprev := st105_p132
  have hstep := st105_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p134 : ((1560030258591/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT105 (i+1))
      = (∑ i ∈ Finset.range 133, stT105 (i+1)) + stT105 134 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 133
    simpa using h
  have hprev := st105_p133
  have hstep := st105_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p135 : ((3397055544931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT105 (i+1))
      = (∑ i ∈ Finset.range 134, stT105 (i+1)) + stT105 135 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 134
    simpa using h
  have hprev := st105_p134
  have hstep := st105_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p136 : ((3823784295001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT105 (i+1))
      = (∑ i ∈ Finset.range 135, stT105 (i+1)) + stT105 136 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 135
    simpa using h
  have hprev := st105_p135
  have hstep := st105_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p137 : ((519734327419/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT105 (i+1))
      = (∑ i ∈ Finset.range 136, stT105 (i+1)) + stT105 137 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 136
    simpa using h
  have hprev := st105_p136
  have hstep := st105_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p138 : ((526863170791/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT105 (i+1))
      = (∑ i ∈ Finset.range 137, stT105 (i+1)) + stT105 138 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 137
    simpa using h
  have hprev := st105_p137
  have hstep := st105_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p139 : ((1983600973573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT105 (i+1))
      = (∑ i ∈ Finset.range 138, stT105 (i+1)) + stT105 139 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 138
    simpa using h
  have hprev := st105_p138
  have hstep := st105_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p140 : ((7105130201897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT105 (i+1))
      = (∑ i ∈ Finset.range 139, stT105 (i+1)) + stT105 140 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 139
    simpa using h
  have hprev := st105_p139
  have hstep := st105_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p141 : ((1277683180029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT105 (i+1))
      = (∑ i ∈ Finset.range 140, stT105 (i+1)) + stT105 141 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 140
    simpa using h
  have hprev := st105_p140
  have hstep := st105_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p142 : ((6159821884163/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT105 (i+1))
      = (∑ i ∈ Finset.range 141, stT105 (i+1)) + stT105 142 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 141
    simpa using h
  have hprev := st105_p141
  have hstep := st105_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p143 : ((6531784834489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT105 (i+1))
      = (∑ i ∈ Finset.range 142, stT105 (i+1)) + stT105 143 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 142
    simpa using h
  have hprev := st105_p142
  have hstep := st105_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p144 : ((7306222858047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT105 (i+1))
      = (∑ i ∈ Finset.range 143, stT105 (i+1)) + stT105 144 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 143
    simpa using h
  have hprev := st105_p143
  have hstep := st105_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p145 : ((1617338698539/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT105 (i+1))
      = (∑ i ∈ Finset.range 144, stT105 (i+1)) + stT105 145 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 144
    simpa using h
  have hprev := st105_p144
  have hstep := st105_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p146 : ((848384375249/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT105 (i+1))
      = (∑ i ∈ Finset.range 145, stT105 (i+1)) + stT105 146 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 145
    simpa using h
  have hprev := st105_p145
  have hstep := st105_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p147 : ((8306907970889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT105 (i+1))
      = (∑ i ∈ Finset.range 146, stT105 (i+1)) + stT105 147 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 146
    simpa using h
  have hprev := st105_p146
  have hstep := st105_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p148 : ((7648914125309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT105 (i+1))
      = (∑ i ∈ Finset.range 147, stT105 (i+1)) + stT105 148 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 147
    simpa using h
  have hprev := st105_p147
  have hstep := st105_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p149 : ((6831333697021/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT105 (i+1))
      = (∑ i ∈ Finset.range 148, stT105 (i+1)) + stT105 149 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 148
    simpa using h
  have hprev := st105_p148
  have hstep := st105_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p150 : ((3121607495203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT105 (i+1))
      = (∑ i ∈ Finset.range 149, stT105 (i+1)) + stT105 150 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 149
    simpa using h
  have hprev := st105_p149
  have hstep := st105_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p151 : ((3078343216807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT105 (i+1))
      = (∑ i ∈ Finset.range 150, stT105 (i+1)) + stT105 151 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 150
    simpa using h
  have hprev := st105_p150
  have hstep := st105_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p152 : ((6605615502653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT105 (i+1))
      = (∑ i ∈ Finset.range 151, stT105 (i+1)) + stT105 152 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 151
    simpa using h
  have hprev := st105_p151
  have hstep := st105_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p153 : ((7378944305513/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT105 (i+1))
      = (∑ i ∈ Finset.range 152, stT105 (i+1)) + stT105 153 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 152
    simpa using h
  have hprev := st105_p152
  have hstep := st105_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p154 : ((8124715644251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT105 (i+1))
      = (∑ i ∈ Finset.range 153, stT105 (i+1)) + stT105 154 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 153
    simpa using h
  have hprev := st105_p153
  have hstep := st105_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p155 : ((340469740261/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT105 (i+1))
      = (∑ i ∈ Finset.range 154, stT105 (i+1)) + stT105 155 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 154
    simpa using h
  have hprev := st105_p154
  have hstep := st105_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p156 : ((4187167548091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT105 (i+1))
      = (∑ i ∈ Finset.range 155, stT105 (i+1)) + stT105 156 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 155
    simpa using h
  have hprev := st105_p155
  have hstep := st105_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p157 : ((3889110784723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT105 (i+1))
      = (∑ i ∈ Finset.range 156, stT105 (i+1)) + stT105 157 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 156
    simpa using h
  have hprev := st105_p156
  have hstep := st105_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p158 : ((3492046195807/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT105 (i+1))
      = (∑ i ∈ Finset.range 157, stT105 (i+1)) + stT105 158 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 157
    simpa using h
  have hprev := st105_p157
  have hstep := st105_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p159 : ((3165138265627/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT105 (i+1))
      = (∑ i ∈ Finset.range 158, stT105 (i+1)) + stT105 159 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 158
    simpa using h
  have hprev := st105_p158
  have hstep := st105_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p160 : ((761058407133/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT105 (i+1))
      = (∑ i ∈ Finset.range 159, stT105 (i+1)) + stT105 160 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 159
    simpa using h
  have hprev := st105_p159
  have hstep := st105_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p161 : ((3176892638337/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT105 (i+1))
      = (∑ i ∈ Finset.range 160, stT105 (i+1)) + stT105 161 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 160
    simpa using h
  have hprev := st105_p160
  have hstep := st105_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p162 : ((350606215291/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT105 (i+1))
      = (∑ i ∈ Finset.range 161, stT105 (i+1)) + stT105 162 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 161
    simpa using h
  have hprev := st105_p161
  have hstep := st105_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p163 : ((48709280627/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT105 (i+1))
      = (∑ i ∈ Finset.range 162, stT105 (i+1)) + stT105 163 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 162
    simpa using h
  have hprev := st105_p162
  have hstep := st105_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p164 : ((1048131274319/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT105 (i+1))
      = (∑ i ∈ Finset.range 163, stT105 (i+1)) + stT105 164 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 163
    simpa using h
  have hprev := st105_p163
  have hstep := st105_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p165 : ((855593906903/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT105 (i+1))
      = (∑ i ∈ Finset.range 164, stT105 (i+1)) + stT105 165 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 164
    simpa using h
  have hprev := st105_p164
  have hstep := st105_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p166 : ((164886599311/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT105 (i+1))
      = (∑ i ∈ Finset.range 165, stT105 (i+1)) + stT105 166 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 165
    simpa using h
  have hprev := st105_p165
  have hstep := st105_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p167 : ((3787746494551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT105 (i+1))
      = (∑ i ∈ Finset.range 166, stT105 (i+1)) + stT105 167 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 166
    simpa using h
  have hprev := st105_p166
  have hstep := st105_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p168 : ((680777493881/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT105 (i+1))
      = (∑ i ∈ Finset.range 167, stT105 (i+1)) + stT105 168 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 167
    simpa using h
  have hprev := st105_p167
  have hstep := st105_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p169 : ((6230912458059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT105 (i+1))
      = (∑ i ∈ Finset.range 168, stT105 (i+1)) + stT105 169 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 168
    simpa using h
  have hprev := st105_p168
  have hstep := st105_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p170 : ((6057220962369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT105 (i+1))
      = (∑ i ∈ Finset.range 169, stT105 (i+1)) + stT105 170 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 169
    simpa using h
  have hprev := st105_p169
  have hstep := st105_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p171 : ((6346108858999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT105 (i+1))
      = (∑ i ∈ Finset.range 170, stT105 (i+1)) + stT105 171 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 170
    simpa using h
  have hprev := st105_p170
  have hstep := st105_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p172 : ((6987556778983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT105 (i+1))
      = (∑ i ∈ Finset.range 171, stT105 (i+1)) + stT105 172 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 171
    simpa using h
  have hprev := st105_p171
  have hstep := st105_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p173 : ((7747267003523/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT105 (i+1))
      = (∑ i ∈ Finset.range 172, stT105 (i+1)) + stT105 173 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 172
    simpa using h
  have hprev := st105_p172
  have hstep := st105_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p174 : ((1670807302631/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT105 (i+1))
      = (∑ i ∈ Finset.range 173, stT105 (i+1)) + stT105 174 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 173
    simpa using h
  have hprev := st105_p173
  have hstep := st105_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p175 : ((8596302366019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT105 (i+1))
      = (∑ i ∈ Finset.range 174, stT105 (i+1)) + stT105 175 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 174
    simpa using h
  have hprev := st105_p174
  have hstep := st105_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p176 : ((4196879843691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT105 (i+1))
      = (∑ i ∈ Finset.range 175, stT105 (i+1)) + stT105 176 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 175
    simpa using h
  have hprev := st105_p175
  have hstep := st105_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p177 : ((1955180889351/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT105 (i+1))
      = (∑ i ∈ Finset.range 176, stT105 (i+1)) + stT105 177 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 176
    simpa using h
  have hprev := st105_p176
  have hstep := st105_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p178 : ((1768969782633/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT105 (i+1))
      = (∑ i ∈ Finset.range 177, stT105 (i+1)) + stT105 178 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 177
    simpa using h
  have hprev := st105_p177
  have hstep := st105_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p179 : ((1602864090609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT105 (i+1))
      = (∑ i ∈ Finset.range 178, stT105 (i+1)) + stT105 179 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 178
    simpa using h
  have hprev := st105_p178
  have hstep := st105_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p180 : ((1511896744911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT105 (i+1))
      = (∑ i ∈ Finset.range 179, stT105 (i+1)) + stT105 180 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 179
    simpa using h
  have hprev := st105_p179
  have hstep := st105_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p181 : ((610085068439/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT105 (i+1))
      = (∑ i ∈ Finset.range 180, stT105 (i+1)) + stT105 181 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 180
    simpa using h
  have hprev := st105_p180
  have hstep := st105_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p182 : ((6549575402777/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT105 (i+1))
      = (∑ i ∈ Finset.range 181, stT105 (i+1)) + stT105 182 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 181
    simpa using h
  have hprev := st105_p181
  have hstep := st105_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p183 : ((3622579723963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT105 (i+1))
      = (∑ i ∈ Finset.range 182, stT105 (i+1)) + stT105 183 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 182
    simpa using h
  have hprev := st105_p182
  have hstep := st105_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p184 : ((7963412592909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT105 (i+1))
      = (∑ i ∈ Finset.range 183, stT105 (i+1)) + stT105 184 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 183
    simpa using h
  have hprev := st105_p183
  have hstep := st105_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p185 : ((8477632292719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT105 (i+1))
      = (∑ i ∈ Finset.range 184, stT105 (i+1)) + stT105 185 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 184
    simpa using h
  have hprev := st105_p184
  have hstep := st105_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p186 : ((8629448599469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT105 (i+1))
      = (∑ i ∈ Finset.range 185, stT105 (i+1)) + stT105 186 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 185
    simpa using h
  have hprev := st105_p185
  have hstep := st105_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p187 : ((418782174277/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT105 (i+1))
      = (∑ i ∈ Finset.range 186, stT105 (i+1)) + stT105 187 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 186
    simpa using h
  have hprev := st105_p186
  have hstep := st105_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p188 : ((24368250407/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT105 (i+1))
      = (∑ i ∈ Finset.range 187, stT105 (i+1)) + stT105 188 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 187
    simpa using h
  have hprev := st105_p187
  have hstep := st105_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p189 : ((7073998990259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT105 (i+1))
      = (∑ i ∈ Finset.range 188, stT105 (i+1)) + stT105 189 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 188
    simpa using h
  have hprev := st105_p188
  have hstep := st105_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p190 : ((6422205787241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT105 (i+1))
      = (∑ i ∈ Finset.range 189, stT105 (i+1)) + stT105 190 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 189
    simpa using h
  have hprev := st105_p189
  have hstep := st105_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p191 : ((377176363851/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT105 (i+1))
      = (∑ i ∈ Finset.range 190, stT105 (i+1)) + stT105 191 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 190
    simpa using h
  have hprev := st105_p190
  have hstep := st105_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p192 : ((188212949271/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT105 (i+1))
      = (∑ i ∈ Finset.range 191, stT105 (i+1)) + stT105 192 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 191
    simpa using h
  have hprev := st105_p191
  have hstep := st105_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p193 : ((3192982681531/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT105 (i+1))
      = (∑ i ∈ Finset.range 192, stT105 (i+1)) + stT105 193 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 192
    simpa using h
  have hprev := st105_p192
  have hstep := st105_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p194 : ((3508120294219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT105 (i+1))
      = (∑ i ∈ Finset.range 193, stT105 (i+1)) + stT105 194 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 193
    simpa using h
  have hprev := st105_p193
  have hstep := st105_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p195 : ((773173013703/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT105 (i+1))
      = (∑ i ∈ Finset.range 194, stT105 (i+1)) + stT105 195 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 194
    simpa using h
  have hprev := st105_p194
  have hstep := st105_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p196 : ((833008953867/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT105 (i+1))
      = (∑ i ∈ Finset.range 195, stT105 (i+1)) + stT105 196 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 195
    simpa using h
  have hprev := st105_p195
  have hstep := st105_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p197 : ((864558977889/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT105 (i+1))
      = (∑ i ∈ Finset.range 196, stT105 (i+1)) + stT105 197 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 196
    simpa using h
  have hprev := st105_p196
  have hstep := st105_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p198 : ((859383310413/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT105 (i+1))
      = (∑ i ∈ Finset.range 197, stT105 (i+1)) + stT105 198 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 197
    simpa using h
  have hprev := st105_p197
  have hstep := st105_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p199 : ((4096237020039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT105 (i+1))
      = (∑ i ∈ Finset.range 198, stT105 (i+1)) + stT105 199 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 198
    simpa using h
  have hprev := st105_p198
  have hstep := st105_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_p200 : ((1888372078561/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT105 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT105 (i+1))
      = (∑ i ∈ Finset.range 199, stT105 (i+1)) + stT105 200 := by
    have h := Finset.sum_range_succ (fun i => stT105 (i+1)) 199
    simpa using h
  have hprev := st105_p199
  have hstep := st105_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st105_s200 :
    |Real.sin (((105 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((176023/250000 : ℚ) : ℝ))
      - ((6693/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 6747311/10000000) (δ := 139/20000000) (ψ := 176023/250000) 105 88
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 3200000 in
/-- **The certified detector sign at `t = 105`** (evaluated boundary). -/
theorem station_105_sign : 0 < hardyG (((105:ℕ)):ℝ) := by
  have hcore := phase_station_lower_eval 105 200 (by norm_num) (by norm_num)
    ((176023/250000 : ℚ) : ℝ)
  have hchain := st105_p200
  have hbridge : (∑ i ∈ Finset.range 200, stT105 (i+1))
      = ∑ i ∈ Finset.range 200,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((105:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((176023/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_200
  have hsh := rpow_half_shifts (N := 200) (by norm_num)
  have hcosb := abs_le.mp st105_c200
  have hsinb := abs_le.mp st105_s200
  have hbdy_lo : ((-31487778058903/551262500000000 : ℚ) : ℝ)
      ≤ ((200:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos ((((105:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((176023/250000 : ℚ) : ℝ))) / 2
          - (((105:ℕ)):ℝ)
            * Real.sin ((((105:ℕ)):ℝ) * Real.log ((200:ℕ)) - ((176023/250000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + (((105:ℕ)):ℝ) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((105:ℝ) * Real.log ((200:ℝ)) - ((176023/250000 : ℚ) : ℝ))) / 2
        - (105:ℝ) * Real.sin ((105:ℝ) * Real.log ((200:ℝ)) - ((176023/250000 : ℚ) : ℝ))
        ≥ ((-44530429/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hEneg : -(Real.cos ((105:ℝ) * Real.log ((200:ℝ)) - ((176023/250000 : ℚ) : ℝ))) / 2
        - (105:ℝ) * Real.sin ((105:ℝ) * Real.log ((200:ℝ)) - ((176023/250000 : ℚ) : ℝ))
        ≤ 0 := by
      nlinarith [hcosb.1, hsinb.1,
        Real.neg_one_le_cos ((105:ℝ) * Real.log ((200:ℝ)) - ((176023/250000 : ℚ) : ℝ)),
        Real.neg_one_le_sin ((105:ℝ) * Real.log ((200:ℝ)) - ((176023/250000 : ℚ) : ℝ))]
    have hsqpos : (0:ℝ) ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (200:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + (105:ℝ) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-44530429/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (200:ℝ) * (707107/10000000)
          * ((-44530429/1000000 : ℚ) : ℝ)
        ≤ (200:ℝ) * ((200:ℝ) ^ (-(1/2:ℝ)))
          * ((-44530429/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((200:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((105:ℕ)):ℝ)+1) * ((((105:ℕ)):ℝ)+2) / 8
        * (((200:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((200:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1785737210191/4800000000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((1888372078561/2500000000000 : ℚ) : ℝ) + ((-31487778058903/551262500000000 : ℚ) : ℝ)
      - ((1785737210191/4800000000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((176023/250000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line (((105:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((176023/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((105:ℕ)):ℝ))).re
      - Real.sin ((176023/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((105:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((105:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((105:ℕ)):ℝ)
      = ((((105:ℕ)):ℝ) * (Real.log (((105:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((105:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_105
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
  have hθwin : |(((176023/250000 : ℚ) : ℝ) + ((15:ℤ)) * (2*Real.pi)) - theta (((105:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((105:ℕ)):ℝ))
    (φ := ((176023/250000 : ℚ) : ℝ) + ((15:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((176023/250000 : ℚ)) : ℝ) 15).1,
    (cos_sin_shift (((176023/250000 : ℚ)) : ℝ) 15).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_105_sign
end AxiomAudit
