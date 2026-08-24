import RequestProject.DVPSqrtTable

/-!
# Station `t = 32` of the Hardy ladder (sign -)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT32 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((32 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((45783/200000 : ℚ) : ℝ))

theorem st32_c1 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((973913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4471/78125) (δ := 21/100000000) (ψ := 45783/200000) 32 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t1 : ((973863/1000000 : ℚ) : ℝ) ≤ stT32 1 := by
  have hc : ((973863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((973863/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((973863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c2 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-499613/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7755597/10000000) (δ := 127/50000000) (ψ := 45783/200000) 32 3
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t2 : ((-441621784173/625000000000 : ℚ) : ℝ) ≤ stT32 2 := by
  have hc : ((-249819/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-441621784173/625000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-249819/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c3 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-932631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1732771/2500000) (δ := 143/50000000) (ψ := 45783/200000) 32 6
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t3 : ((-5384836551543/10000000000000 : ℚ) : ℝ) ≤ stT32 3 := by
  have hc : ((-932681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5384836551543/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-932681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c4 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((49437/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 375519/10000000) (δ := 217/100000000) (ψ := 45783/200000) 32 7
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t4 : ((98869/200000 : ℚ) : ℝ) ≤ stT32 4 := by
  have hc : ((98869/100000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98869/200000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((98869/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c5 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((266939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2519039/10000000) (δ := 37/12500000) (ψ := 45783/200000) 32 8
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t5 : ((119367544139/500000000000 : ℚ) : ℝ) ≤ stT32 5 := by
  have hc : ((133457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119367544139/500000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((133457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c6 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((423967/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1396801/10000000) (δ := 119/50000000) (ψ := 45783/200000) 32 9
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t6 : ((432683896011/1250000000000 : ℚ) : ℝ) ≤ stT32 6 := by
  have hc : ((211971/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432683896011/1250000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((211971/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c7 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((702677/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -494777/2500000) (δ := 169/100000000) (ψ := 45783/200000) 32 10
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t7 : ((663919981197/2500000000000 : ℚ) : ℝ) ≤ stT32 7 := by
  have hc : ((702627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((663919981197/2500000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((702627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c8 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-58927/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -87557/125000) (δ := 23/12500000) (ψ := 45783/200000) 32 11
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t8 : ((-833397842247/2500000000000 : ℚ) : ℝ) ≤ stT32 8 := by
  have hc : ((-471441/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-833397842247/2500000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-471441/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c9 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((28379/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2418083/10000000) (δ := 259/100000000) (ψ := 45783/200000) 32 11
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t9 : ((189176647749/1000000000000 : ℚ) : ℝ) ≤ stT32 9 := by
  have hc : ((56753/100000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189176647749/1000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((56753/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c10 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-364987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4861039/10000000) (δ := 31/10000000) (ψ := 45783/200000) 32 12
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t10 : ((-577174237143/5000000000000 : ℚ) : ℝ) ≤ stT32 10 := by
  have hc : ((-365037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-577174237143/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-365037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c11 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((448679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 110551/400000) (δ := 23/10000000) (ψ := 45783/200000) 32 12
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t11 : ((1352667130077/10000000000000 : ℚ) : ℝ) ≤ stT32 11 := by
  have hc : ((448629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1352667130077/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((448629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c12 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-732859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2991639/5000000) (δ := 81/50000000) (ψ := 45783/200000) 32 13
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t12 : ((-66116453799/312500000000 : ℚ) : ℝ) ≤ stT32 12 := by
  have hc : ((-732909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66116453799/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-732909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c13 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((123239/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 420139/10000000) (δ := 201/100000000) (ψ := 45783/200000) 32 13
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t13 : ((2734288257/10000000000 : ℚ) : ℝ) ≤ stT32 13 := by
  have hc : ((492931/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2734288257/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((492931/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c14 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-412079/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 793597/1250000) (δ := 121/50000000) (ψ := 45783/200000) 32 13
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t14 : ((-137674313469/625000000000 : ℚ) : ℝ) ≤ stT32 14 := by
  have hc : ((-51513/62500 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137674313469/625000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-51513/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c15 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((17443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3839757/10000000) (δ := 311/100000000) (ψ := 45783/200000) 32 14
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t15 : ((5621633373/625000000000 : ℚ) : ℝ) ≤ stT32 15 := by
  have hc : ((8709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5621633373/625000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((8709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c16 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((431573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52933/400000) (δ := 231/100000000) (ψ := 45783/200000) 32 14
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t16 : ((107887/500000 : ℚ) : ℝ) ≤ stT32 16 := by
  have hc : ((107887/125000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107887/500000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((107887/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c17 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-782407/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3086647/5000000) (δ := 191/100000000) (ψ := 45783/200000) 32 14
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t17 : ((-1897737562149/10000000000000 : ℚ) : ℝ) ≤ stT32 17 := by
  have hc : ((-782457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1897737562149/10000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-782457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c18 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-402277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1240499/2500000) (δ := 91/50000000) (ψ := 45783/200000) 32 15
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t18 : ((-948293992521/10000000000000 : ℚ) : ℝ) ≤ stT32 18 := by
  have hc : ((-402327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-948293992521/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-402327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c19 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((120969/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -318309/5000000) (δ := 131/50000000) (ψ := 45783/200000) 32 15
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t19 : ((1110030158607/5000000000000 : ℚ) : ℝ) ≤ stT32 19 := by
  have hc : ((483851/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1110030158607/5000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((483851/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c20 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((183021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 693369/2000000) (δ := 111/50000000) (ψ := 45783/200000) 32 15
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t20 : ((409135415057/10000000000000 : ℚ) : ℝ) ≤ stT32 20 := by
  have hc : ((182971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409135415057/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((182971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c21 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-245331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3685029/5000000) (δ := 221/100000000) (ψ := 45783/200000) 32 15
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t21 : ((-1070766866973/5000000000000 : ℚ) : ℝ) ≤ stT32 21 := by
  have hc : ((-490687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1070766866973/5000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-490687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c22 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-54449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -288519/625000) (δ := 17/10000000) (ψ := 45783/200000) 32 16
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t22 : ((-14513377959/250000000000 : ℚ) : ℝ) ≤ stT32 22 := by
  have hc : ((-54459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14513377959/250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-54459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c23 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((14241/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1060163/10000000) (δ := 29/10000000) (ψ := 45783/200000) 32 16
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t23 : ((118771626741/625000000000 : ℚ) : ℝ) ≤ stT32 23 := by
  have hc : ((455687/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118771626741/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((455687/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c24 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((591529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2344607/10000000) (δ := 21/10000000) (ψ := 45783/200000) 32 16
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t24 : ((1207351185439/10000000000000 : ℚ) : ℝ) ≤ stT32 24 := by
  have hc : ((591479/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1207351185439/10000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((591479/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c25 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-77951/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2805183/5000000) (δ := 1/400000) (ψ := 45783/200000) 32 16
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t25 : ((-623658311829/5000000000000 : ℚ) : ℝ) ≤ stT32 25 := by
  have hc : ((-311829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-623658311829/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-311829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c26 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-468367/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -347997/500000) (δ := 199/100000000) (ψ := 45783/200000) 32 17
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t26 : ((-57412036969/312500000000 : ℚ) : ℝ) ≤ stT32 26 := by
  have hc : ((-58549/62500 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57412036969/312500000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-58549/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c27 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-5489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1970357/5000000) (δ := 51/25000000) (ψ := 45783/200000) 32 17
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t27 : ((-10659811039/10000000000000 : ℚ) : ℝ) ≤ stT32 27 := by
  have hc : ((-5539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10659811039/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-5539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c28 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((916113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -515651/5000000) (δ := 279/100000000) (ψ := 45783/200000) 32 17
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t28 : ((865598005393/5000000000000 : ℚ) : ℝ) ≤ stT32 28 := by
  have hc : ((916063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((865598005393/5000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((916063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c29 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((7581/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1776003/10000000) (δ := 239/100000000) (ψ := 45783/200000) 32 17
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t29 : ((28153264433/200000000000 : ℚ) : ℝ) ≤ stT32 29 := by
  have hc : ((15161/20000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28153264433/200000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((15161/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c30 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-8903/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4488127/10000000) (δ := 61/25000000) (ψ := 45783/200000) 32 17
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t30 : ((-1625823251/40000000000 : ℚ) : ℝ) ≤ stT32 30 := by
  have hc : ((-1781/8000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1625823251/40000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-1781/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c31 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-956199/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7111313/10000000) (δ := 319/100000000) (ψ := 45783/200000) 32 17
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t31 : ((-858737420723/5000000000000 : ℚ) : ℝ) ≤ stT32 31 := by
  have hc : ((-956249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-858737420723/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-956249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c32 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-94067/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3028377/5000000) (δ := 309/100000000) (ψ := 45783/200000) 32 18
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t32 : ((-665198347731/5000000000000 : ℚ) : ℝ) ≤ stT32 32 := by
  have hc : ((-376293/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-665198347731/5000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-376293/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c33 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((66199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3595021/10000000) (δ := 107/50000000) (ψ := 45783/200000) 32 18
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t33 : ((7199631939/312500000000 : ℚ) : ℝ) ≤ stT32 33 := by
  have hc : ((33087/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7199631939/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((33087/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c34 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((885739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9428/78125) (δ := 229/100000000) (ψ := 45783/200000) 32 18
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t34 : ((303788669933/2000000000000 : ℚ) : ℝ) ≤ stT32 34 := by
  have hc : ((885689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((303788669933/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((885689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c35 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((902659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1112219/10000000) (δ := 107/50000000) (ψ := 45783/200000) 32 18
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t35 : ((381421803393/2500000000000 : ℚ) : ℝ) ≤ stT32 35 := by
  have hc : ((902609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381421803393/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((902609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c36 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((222561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3365889/10000000) (δ := 189/100000000) (ψ := 45783/200000) 32 18
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t36 : ((185425759163/5000000000000 : ℚ) : ℝ) ≤ stT32 36 := by
  have hc : ((222511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185425759163/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((222511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c37 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-607037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5557807/10000000) (δ := 269/100000000) (ψ := 45783/200000) 32 18
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t37 : ((-99804495713/1000000000000 : ℚ) : ℝ) ≤ stT32 37 := by
  have hc : ((-607087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99804495713/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-607087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c38 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-997883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3845633/5000000) (δ := 87/50000000) (ψ := 45783/200000) 32 18
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t38 : ((-323772376319/2000000000000 : ℚ) : ℝ) ≤ stT32 38 := by
  have hc : ((-997933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-323772376319/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-997933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c39 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-3603/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2969329/5000000) (δ := 89/50000000) (ψ := 45783/200000) 32 19
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t39 : ((-11539638733/100000000000 : ℚ) : ℝ) ≤ stT32 39 := by
  have hc : ((-14413/20000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11539638733/100000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-14413/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c40 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((5503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3913233/10000000) (δ := 37/20000000) (ψ := 45783/200000) 32 19
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t40 : ((4310972757/5000000000000 : ℚ) : ℝ) ≤ stT32 40 := by
  have hc : ((5453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4310972757/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((5453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c41 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((71433/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -60557/312500) (δ := 9/4000000) (ψ := 45783/200000) 32 19
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t41 : ((27887937609/250000000000 : ℚ) : ℝ) ≤ stT32 41 := by
  have hc : ((17857/25000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27887937609/250000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((17857/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c42 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -501/500000) (δ := 129/50000000) (ψ := 45783/200000) 32 19
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t42 : ((771471752043/5000000000000 : ℚ) : ℝ) ≤ stT32 42 := by
  have hc : ((499971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((771471752043/5000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((499971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c43 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((91549/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 93621/500000) (δ := 129/50000000) (ψ := 45783/200000) 32 19
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t43 : ((111681056487/1000000000000 : ℚ) : ℝ) ≤ stT32 43 := by
  have hc : ((366171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111681056487/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((366171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c44 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((86057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3711581/10000000) (δ := 109/50000000) (ψ := 45783/200000) 32 19
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t44 : ((32415092223/2500000000000 : ℚ) : ℝ) ≤ stT32 44 := by
  have hc : ((86007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32415092223/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((86007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c45 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-29577/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 550941/1000000) (δ := 61/20000000) (ψ := 45783/200000) 32 19
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t45 : ((-11023628901/125000000000 : ℚ) : ℝ) ≤ stT32 45 := by
  have hc : ((-59159/100000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11023628901/125000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-59159/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c46 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-97263/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3633861/5000000) (δ := 61/20000000) (ψ := 45783/200000) 32 19
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t46 : ((-1792673557/12500000000 : ℚ) : ℝ) ≤ stT32 46 := by
  have hc : ((-24317/25000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1792673557/12500000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-24317/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c47 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-449417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1343949/2000000) (δ := 327/100000000) (ψ := 45783/200000) 32 20
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t47 : ((-6555785733/50000000000 : ℚ) : ℝ) ≤ stT32 47 := by
  have hc : ((-224721/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6555785733/50000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-224721/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c48 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-214503/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -314717/625000) (δ := 287/100000000) (ψ := 45783/200000) 32 20
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t48 : ((-75596818/1220703125 : ℚ) : ℝ) ≤ stT32 48 := by
  have hc : ((-6704/15625 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75596818/1220703125 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-6704/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c49 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((214739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3385929/10000000) (δ := 79/25000000) (ψ := 45783/200000) 32 20
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t49 : ((306698479419/10000000000000 : ℚ) : ℝ) ≤ stT32 49 := by
  have hc : ((214689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((306698479419/10000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((214689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c50 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((759739/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -110607/625000) (δ := 287/100000000) (ψ := 45783/200000) 32 20
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t50 : ((1074362059757/10000000000000 : ℚ) : ℝ) ≤ stT32 50 := by
  have hc : ((759689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1074362059757/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((759689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c51 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((15582/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -92751/5000000) (δ := 207/100000000) (ψ := 45783/200000) 32 20
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t51 : ((17454455193/125000000000 : ℚ) : ℝ) ≤ stT32 51 := by
  have hc : ((498599/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17454455193/125000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((498599/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c52 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((213499/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 273589/2000000) (δ := 247/100000000) (ψ := 45783/200000) 32 20
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t52 : ((2368419231/20000000000 : ℚ) : ℝ) ≤ stT32 52 := by
  have hc : ((426973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2368419231/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((426973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c53 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((50293/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14459/50000) (δ := 287/100000000) (ψ := 45783/200000) 32 20
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t53 : ((55259304987/1000000000000 : ℚ) : ℝ) ≤ stT32 53 := by
  have hc : ((201147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55259304987/1000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((201147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c54 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-91517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4387171/10000000) (δ := 167/100000000) (ψ := 45783/200000) 32 20
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t54 : ((-15571614597/625000000000 : ℚ) : ℝ) ≤ stT32 54 := by
  have hc : ((-45771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15571614597/625000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-45771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c55 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-174257/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2927551/5000000) (δ := 69/25000000) (ψ := 45783/200000) 32 20
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t55 : ((-1174924969/12500000000 : ℚ) : ℝ) ≤ stT32 55 := by
  have hc : ((-348539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1174924969/12500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-348539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c56 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-975247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3648291/5000000) (δ := 69/25000000) (ψ := 45783/200000) 32 20
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t56 : ((-1303296208179/10000000000000 : ℚ) : ℝ) ≤ stT32 56 := by
  have hc : ((-975297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1303296208179/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-975297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c57 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-470803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1399083/2000000) (δ := 207/100000000) (ψ := 45783/200000) 32 21
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t57 : ((-155906805831/1250000000000 : ℚ) : ℝ) ≤ stT32 57 := by
  have hc : ((-117707/125000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155906805831/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-117707/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c58 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-621639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224163/400000) (δ := 69/25000000) (ψ := 45783/200000) 32 21
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t58 : ((-163263613357/2000000000000 : ℚ) : ℝ) ≤ stT32 58 := by
  have hc : ((-621689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163263613357/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-621689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c59 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-15437/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4236521/10000000) (δ := 49/25000000) (ψ := 45783/200000) 32 21
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t59 : ((-8042165097/500000000000 : ℚ) : ℝ) ≤ stT32 59 := by
  have hc : ((-61773/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8042165097/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-61773/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c60 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((402289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2891951/10000000) (δ := 207/100000000) (ψ := 45783/200000) 32 21
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t60 : ((259644067783/5000000000000 : ℚ) : ℝ) ≤ stT32 60 := by
  have hc : ((402239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((259644067783/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((402239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c61 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((809297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1569607/10000000) (δ := 207/100000000) (ψ := 45783/200000) 32 21
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t61 : ((64758372681/625000000000 : ℚ) : ℝ) ≤ stT32 61 := by
  have hc : ((809247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64758372681/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((809247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c62 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((994227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -53753/2000000) (δ := 287/100000000) (ψ := 45783/200000) 32 21
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t62 : ((1262605784177/10000000000000 : ℚ) : ℝ) ≤ stT32 62 := by
  have hc : ((994177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1262605784177/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((994177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c63 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((919297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 505631/5000000) (δ := 59/25000000) (ψ := 45783/200000) 32 21
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t63 : ((1158141829607/10000000000000 : ℚ) : ℝ) ≤ stT32 63 := by
  have hc : ((919247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1158141829607/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((919247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c64 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((614967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2271131/10000000) (δ := 287/100000000) (ψ := 45783/200000) 32 21
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t64 : ((614917/8000000 : ℚ) : ℝ) ≤ stT32 64 := by
  have hc : ((614917/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((614917/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((614917/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c65 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((82723/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 702293/2000000) (δ := 207/100000000) (ψ := 45783/200000) 32 21
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t65 : ((51287108103/2500000000000 : ℚ) : ℝ) ≤ stT32 65 := by
  have hc : ((41349/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51287108103/2500000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((41349/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c66 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-63359/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4732863/10000000) (δ := 49/25000000) (ψ := 45783/200000) 32 21
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t66 : ((-15600370527/400000000000 : ℚ) : ℝ) ≤ stT32 66 := by
  have hc : ((-63369/200000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15600370527/400000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-63369/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c67 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-89979/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5935893/10000000) (δ := 69/25000000) (ψ := 45783/200000) 32 21
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t67 : ((-87947623999/1000000000000 : ℚ) : ℝ) ≤ stT32 67 := by
  have hc : ((-359941/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87947623999/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-359941/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c68 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-478669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71211/100000) (δ := 79/25000000) (ψ := 45783/200000) 32 21
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t68 : ((-290251080613/2500000000000 : ℚ) : ℝ) ≤ stT32 68 := by
  have hc : ((-239347/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-290251080613/2500000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-239347/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c69 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-984899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7418959/10000000) (δ := 153/50000000) (ψ := 45783/200000) 32 22
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t69 : ((-1185739718191/10000000000000 : ℚ) : ℝ) ≤ stT32 69 := by
  have hc : ((-984949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1185739718191/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-984949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c70 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-805399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313393/500000) (δ := 93/50000000) (ψ := 45783/200000) 32 22
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t70 : ((-962696002821/10000000000000 : ℚ) : ℝ) ≤ stT32 70 := by
  have hc : ((-805449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-962696002821/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-805449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c71 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-463941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5133089/10000000) (δ := 257/100000000) (ψ := 45783/200000) 32 22
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t71 : ((-275328083481/5000000000000 : ℚ) : ℝ) ≤ stT32 71 := by
  have hc : ((-463991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275328083481/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-463991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c72 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-34873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401419/1000000) (δ := 133/50000000) (ψ := 45783/200000) 32 22
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t72 : ((-2572323411/625000000000 : ℚ) : ℝ) ≤ stT32 72 := by
  have hc : ((-34923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2572323411/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-34923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c73 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((395403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -727681/2500000) (δ := 93/50000000) (ψ := 45783/200000) 32 22
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t73 : ((462725500083/10000000000000 : ℚ) : ℝ) ≤ stT32 73 := by
  have hc : ((395353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((462725500083/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((395353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c74 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((372951/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28473/156250) (δ := 297/100000000) (ψ := 45783/200000) 32 22
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t74 : ((54189690597/625000000000 : ℚ) : ℝ) ≤ stT32 74 := by
  have hc : ((186463/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54189690597/625000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((186463/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c75 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((477761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74843/1000000) (δ := 133/50000000) (ψ := 45783/200000) 32 22
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t75 : ((689552199/6250000000 : ℚ) : ℝ) ≤ stT32 75 := by
  have hc : ((59717/62500 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((689552199/6250000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((59717/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c76 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((992263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 77797/2500000) (δ := 93/50000000) (ψ := 45783/200000) 32 22
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t76 : ((569072851807/5000000000000 : ℚ) : ℝ) ≤ stT32 76 := by
  have hc : ((992213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((569072851807/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((992213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c77 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((34251/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 678477/5000000) (δ := 133/50000000) (ψ := 45783/200000) 32 22
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t77 : ((7806066329/80000000000 : ℚ) : ℝ) ≤ stT32 77 := by
  have hc : ((34249/40000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7806066329/80000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((34249/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c78 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((115409/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2389227/10000000) (δ := 113/50000000) (ψ := 45783/200000) 32 22
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t78 : ((130663633523/2000000000000 : ℚ) : ℝ) ≤ stT32 78 := by
  have hc : ((115399/200000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130663633523/2000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((115399/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c79 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((51493/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3408349/10000000) (δ := 177/100000000) (ψ := 45783/200000) 32 22
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t79 : ((115840082607/5000000000000 : ℚ) : ℝ) ≤ stT32 79 := by
  have hc : ((102961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115840082607/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((102961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c80 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-193829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4414651/10000000) (δ := 113/50000000) (ψ := 45783/200000) 32 22
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t80 : ((-108381656943/5000000000000 : ℚ) : ℝ) ≤ stT32 80 := by
  have hc : ((-193879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108381656943/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-193879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c81 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-558507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5408453/10000000) (δ := 177/100000000) (ψ := 45783/200000) 32 22
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t81 : ((-77577423173/1250000000000 : ℚ) : ℝ) ≤ stT32 81 := by
  have hc : ((-558557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77577423173/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-558557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c82 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-416699/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 319503/500000) (δ := 93/50000000) (ψ := 45783/200000) 32 22
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t82 : ((-28762186299/312500000000 : ℚ) : ℝ) ≤ stT32 82 := by
  have hc : ((-104181/125000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28762186299/312500000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-104181/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c83 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-245131/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7359769/10000000) (δ := 153/50000000) (ψ := 45783/200000) 32 22
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t83 : ((-538160093541/5000000000000 : ℚ) : ℝ) ≤ stT32 83 := by
  have hc : ((-490287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-538160093541/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-490287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c84 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-491417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7390099/10000000) (δ := 67/20000000) (ψ := 45783/200000) 32 23
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t84 : ((-26810372589/250000000000 : ℚ) : ℝ) ≤ stT32 84 := by
  have hc : ((-245721/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26810372589/250000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-245721/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c85 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-844987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3221671/5000000) (δ := 47/25000000) (ψ := 45783/200000) 32 23
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t85 : ((-916571917161/10000000000000 : ℚ) : ℝ) ≤ stT32 85 := by
  have hc : ((-845037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-916571917161/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-845037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c86 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-23639/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5507659/10000000) (δ := 77/25000000) (ψ := 45783/200000) 32 23
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t86 : ((-3186594031/50000000000 : ℚ) : ℝ) ≤ stT32 86 := by
  have hc : ((-23641/40000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3186594031/50000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-23641/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c87 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-259323/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4582793/10000000) (δ := 51/20000000) (ψ := 45783/200000) 32 23
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t87 : ((-278077165149/10000000000000 : ℚ) : ℝ) ≤ stT32 87 := by
  have hc : ((-259373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278077165149/10000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-259373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c88 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((103213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1834249/5000000) (δ := 59/20000000) (ψ := 45783/200000) 32 23
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t88 : ((109972067489/10000000000000 : ℚ) : ℝ) ≤ stT32 88 := by
  have hc : ((103163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109972067489/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((103163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c89 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((56051/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2764533/10000000) (δ := 57/25000000) (ψ := 45783/200000) 32 23
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t89 : ((237629067463/5000000000000 : ℚ) : ℝ) ≤ stT32 89 := by
  have hc : ((224179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((237629067463/5000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((224179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c90 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((732869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1870669/10000000) (δ := 57/25000000) (ψ := 45783/200000) 32 23
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t90 : ((193114661337/2500000000000 : ℚ) : ℝ) ≤ stT32 90 := by
  have hc : ((732819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193114661337/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((732819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c91 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((461561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493341/5000000) (δ := 87/25000000) (ψ := 45783/200000) 32 23
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t91 : ((3779850033/39062500000 : ℚ) : ℝ) ≤ stT32 91 := by
  have hc : ((14423/15625 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3779850033/39062500000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((14423/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c92 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((99899/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -28089/2500000) (δ := 67/25000000) (ψ := 45783/200000) 32 23
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t92 : ((13018335921/125000000000 : ℚ) : ℝ) ≤ stT32 92 := by
  have hc : ((49947/50000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13018335921/125000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((49947/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c93 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((477519/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 752517/10000000) (δ := 77/25000000) (ψ := 45783/200000) 32 23
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t93 : ((247568940397/2500000000000 : ℚ) : ℝ) ≤ stT32 93 := by
  have hc : ((238747/250000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((247568940397/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((238747/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c94 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((800147/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80407/500000) (δ := 67/25000000) (ψ := 45783/200000) 32 23
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t94 : ((825236847837/10000000000000 : ℚ) : ℝ) ≤ stT32 94 := by
  have hc : ((800097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((825236847837/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((800097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c95 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((555457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2454709/10000000) (δ := 77/25000000) (ψ := 45783/200000) 32 23
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t95 : ((284917681523/5000000000000 : ℚ) : ℝ) ≤ stT32 95 := by
  have hc : ((555407/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284917681523/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((555407/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c96 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((125557/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3292413/10000000) (δ := 77/25000000) (ψ := 45783/200000) 32 23
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t96 : ((1601505873/62500000000 : ℚ) : ℝ) ≤ stT32 96 := by
  have hc : ((31383/125000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1601505873/62500000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((31383/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c97 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-777/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1030359/2500000) (δ := 67/25000000) (ψ := 45783/200000) 32 23
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t97 : ((-315772917/40000000000 : ℚ) : ℝ) ≤ stT32 97 := by
  have hc : ((-311/4000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-315772917/40000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-311/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c98 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-15797/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1235489/2500000) (δ := 67/25000000) (ψ := 45783/200000) 32 23
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t98 : ((-15959407247/400000000000 : ℚ) : ℝ) ≤ stT32 98 := by
  have hc : ((-15799/40000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15959407247/400000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-15799/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c99 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-667511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1150829/2000000) (δ := 7/4000000) (ψ := 45783/200000) 32 23
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t99 : ((-335462086159/5000000000000 : ℚ) : ℝ) ≤ stT32 99 := by
  have hc : ((-667561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-335462086159/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-667561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_c100 :
    |Real.cos (((32 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((45783/200000 : ℚ) : ℝ))
      - ((-868651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1639543/2500000) (δ := 67/25000000) (ψ := 45783/200000) 32 23
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st32_t100 : ((-868701/10000000 : ℚ) : ℝ) ≤ stT32 100 := by
  have hc : ((-868701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((32 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((45783/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st32_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-868701/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-868701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st32_p1 : ((973863/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT32 (i+1) := by
  rw [Finset.sum_range_one]
  exact st32_t1

theorem st32_p2 : ((167042590827/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT32 (i+1))
      = (∑ i ∈ Finset.range 1, stT32 (i+1)) + stT32 2 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 1
    simpa using h
  have hprev := st32_p1
  have hstep := st32_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p3 : ((-2712155098311/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT32 (i+1))
      = (∑ i ∈ Finset.range 2, stT32 (i+1)) + stT32 3 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 2
    simpa using h
  have hprev := st32_p2
  have hstep := st32_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p4 : ((2231294901689/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT32 (i+1))
      = (∑ i ∈ Finset.range 3, stT32 (i+1)) + stT32 4 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 3
    simpa using h
  have hprev := st32_p3
  have hstep := st32_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p5 : ((4618645784469/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT32 (i+1))
      = (∑ i ∈ Finset.range 4, stT32 (i+1)) + stT32 5 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 4
    simpa using h
  have hprev := st32_p4
  have hstep := st32_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p6 : ((8080116952557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT32 (i+1))
      = (∑ i ∈ Finset.range 5, stT32 (i+1)) + stT32 6 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 5
    simpa using h
  have hprev := st32_p5
  have hstep := st32_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p7 : ((2147159375469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT32 (i+1))
      = (∑ i ∈ Finset.range 6, stT32 (i+1)) + stT32 7 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 6
    simpa using h
  have hprev := st32_p6
  have hstep := st32_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p8 : ((7402205508357/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT32 (i+1))
      = (∑ i ∈ Finset.range 7, stT32 (i+1)) + stT32 8 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 7
    simpa using h
  have hprev := st32_p7
  have hstep := st32_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p9 : ((9293971985847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT32 (i+1))
      = (∑ i ∈ Finset.range 8, stT32 (i+1)) + stT32 9 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 8
    simpa using h
  have hprev := st32_p8
  have hstep := st32_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p10 : ((8139623511561/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT32 (i+1))
      = (∑ i ∈ Finset.range 9, stT32 (i+1)) + stT32 10 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 9
    simpa using h
  have hprev := st32_p9
  have hstep := st32_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p11 : ((4746145320819/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT32 (i+1))
      = (∑ i ∈ Finset.range 10, stT32 (i+1)) + stT32 11 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 10
    simpa using h
  have hprev := st32_p10
  have hstep := st32_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p12 : ((737656412007/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT32 (i+1))
      = (∑ i ∈ Finset.range 11, stT32 (i+1)) + stT32 12 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 11
    simpa using h
  have hprev := st32_p11
  have hstep := st32_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p13 : ((1011085237707/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT32 (i+1))
      = (∑ i ∈ Finset.range 12, stT32 (i+1)) + stT32 13 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 12
    simpa using h
  have hprev := st32_p12
  have hstep := st32_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p14 : ((3954031680783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT32 (i+1))
      = (∑ i ∈ Finset.range 13, stT32 (i+1)) + stT32 14 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 13
    simpa using h
  have hprev := st32_p13
  have hstep := st32_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p15 : ((3999004747767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT32 (i+1))
      = (∑ i ∈ Finset.range 14, stT32 (i+1)) + stT32 15 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 14
    simpa using h
  have hprev := st32_p14
  have hstep := st32_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p16 : ((5077874747767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT32 (i+1))
      = (∑ i ∈ Finset.range 15, stT32 (i+1)) + stT32 16 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 15
    simpa using h
  have hprev := st32_p15
  have hstep := st32_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p17 : ((1651602386677/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT32 (i+1))
      = (∑ i ∈ Finset.range 16, stT32 (i+1)) + stT32 17 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 16
    simpa using h
  have hprev := st32_p16
  have hstep := st32_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p18 : ((57107171413/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT32 (i+1))
      = (∑ i ∈ Finset.range 17, stT32 (i+1)) + stT32 18 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 17
    simpa using h
  have hprev := st32_p17
  have hstep := st32_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p19 : ((4764889129039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT32 (i+1))
      = (∑ i ∈ Finset.range 18, stT32 (i+1)) + stT32 19 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 18
    simpa using h
  have hprev := st32_p18
  have hstep := st32_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p20 : ((1987782734627/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT32 (i+1))
      = (∑ i ∈ Finset.range 19, stT32 (i+1)) + stT32 20 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 19
    simpa using h
  have hprev := st32_p19
  have hstep := st32_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p21 : ((7797379939189/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT32 (i+1))
      = (∑ i ∈ Finset.range 20, stT32 (i+1)) + stT32 21 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 20
    simpa using h
  have hprev := st32_p20
  have hstep := st32_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p22 : ((7216844820829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT32 (i+1))
      = (∑ i ∈ Finset.range 21, stT32 (i+1)) + stT32 22 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 21
    simpa using h
  have hprev := st32_p21
  have hstep := st32_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p23 : ((1823438169737/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT32 (i+1))
      = (∑ i ∈ Finset.range 22, stT32 (i+1)) + stT32 23 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 22
    simpa using h
  have hprev := st32_p22
  have hstep := st32_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p24 : ((2581135508531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT32 (i+1))
      = (∑ i ∈ Finset.range 23, stT32 (i+1)) + stT32 24 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 23
    simpa using h
  have hprev := st32_p23
  have hstep := st32_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p25 : ((4538612705233/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT32 (i+1))
      = (∑ i ∈ Finset.range 24, stT32 (i+1)) + stT32 25 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 24
    simpa using h
  have hprev := st32_p24
  have hstep := st32_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p26 : ((3620020113729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT32 (i+1))
      = (∑ i ∈ Finset.range 25, stT32 (i+1)) + stT32 26 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 25
    simpa using h
  have hprev := st32_p25
  have hstep := st32_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p27 : ((7229380416419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT32 (i+1))
      = (∑ i ∈ Finset.range 26, stT32 (i+1)) + stT32 27 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 26
    simpa using h
  have hprev := st32_p26
  have hstep := st32_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p28 : ((1792115285441/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT32 (i+1))
      = (∑ i ∈ Finset.range 27, stT32 (i+1)) + stT32 28 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 27
    simpa using h
  have hprev := st32_p27
  have hstep := st32_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p29 : ((2073647929771/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT32 (i+1))
      = (∑ i ∈ Finset.range 28, stT32 (i+1)) + stT32 29 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 28
    simpa using h
  have hprev := st32_p28
  have hstep := st32_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p30 : ((1992356767221/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT32 (i+1))
      = (∑ i ∈ Finset.range 29, stT32 (i+1)) + stT32 30 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 29
    simpa using h
  have hprev := st32_p29
  have hstep := st32_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p31 : ((8244308994659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT32 (i+1))
      = (∑ i ∈ Finset.range 30, stT32 (i+1)) + stT32 31 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 30
    simpa using h
  have hprev := st32_p30
  have hstep := st32_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p32 : ((6913912299197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT32 (i+1))
      = (∑ i ∈ Finset.range 31, stT32 (i+1)) + stT32 32 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 31
    simpa using h
  have hprev := st32_p31
  have hstep := st32_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p33 : ((1428860104249/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT32 (i+1))
      = (∑ i ∈ Finset.range 32, stT32 (i+1)) + stT32 33 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 32
    simpa using h
  have hprev := st32_p32
  have hstep := st32_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p34 : ((866324387091/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT32 (i+1))
      = (∑ i ∈ Finset.range 33, stT32 (i+1)) + stT32 34 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 33
    simpa using h
  have hprev := st32_p33
  have hstep := st32_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p35 : ((5094465542241/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT32 (i+1))
      = (∑ i ∈ Finset.range 34, stT32 (i+1)) + stT32 35 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 34
    simpa using h
  have hprev := st32_p34
  have hstep := st32_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p36 : ((1319972825351/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT32 (i+1))
      = (∑ i ∈ Finset.range 35, stT32 (i+1)) + stT32 36 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 35
    simpa using h
  have hprev := st32_p35
  have hstep := st32_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p37 : ((4780868822839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT32 (i+1))
      = (∑ i ∈ Finset.range 36, stT32 (i+1)) + stT32 37 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 36
    simpa using h
  have hprev := st32_p36
  have hstep := st32_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p38 : ((7942875764083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT32 (i+1))
      = (∑ i ∈ Finset.range 37, stT32 (i+1)) + stT32 38 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 37
    simpa using h
  have hprev := st32_p37
  have hstep := st32_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p39 : ((6788911890783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT32 (i+1))
      = (∑ i ∈ Finset.range 38, stT32 (i+1)) + stT32 39 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 38
    simpa using h
  have hprev := st32_p38
  have hstep := st32_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p40 : ((6797533836297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT32 (i+1))
      = (∑ i ∈ Finset.range 39, stT32 (i+1)) + stT32 40 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 39
    simpa using h
  have hprev := st32_p39
  have hstep := st32_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p41 : ((7913051340657/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT32 (i+1))
      = (∑ i ∈ Finset.range 40, stT32 (i+1)) + stT32 41 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 40
    simpa using h
  have hprev := st32_p40
  have hstep := st32_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p42 : ((9455994844743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT32 (i+1))
      = (∑ i ∈ Finset.range 41, stT32 (i+1)) + stT32 42 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 41
    simpa using h
  have hprev := st32_p41
  have hstep := st32_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p43 : ((10572805409613/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT32 (i+1))
      = (∑ i ∈ Finset.range 42, stT32 (i+1)) + stT32 43 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 42
    simpa using h
  have hprev := st32_p42
  have hstep := st32_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p44 : ((2140493155701/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT32 (i+1))
      = (∑ i ∈ Finset.range 43, stT32 (i+1)) + stT32 44 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 43
    simpa using h
  have hprev := st32_p43
  have hstep := st32_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p45 : ((392823018657/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT32 (i+1))
      = (∑ i ∈ Finset.range 44, stT32 (i+1)) + stT32 45 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 44
    simpa using h
  have hprev := st32_p44
  have hstep := st32_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p46 : ((335457464833/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT32 (i+1))
      = (∑ i ∈ Finset.range 45, stT32 (i+1)) + stT32 46 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 45
    simpa using h
  have hprev := st32_p45
  have hstep := st32_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p47 : ((283011178969/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT32 (i+1))
      = (∑ i ∈ Finset.range 46, stT32 (i+1)) + stT32 47 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 46
    simpa using h
  have hprev := st32_p46
  have hstep := st32_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p48 : ((6455990341169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT32 (i+1))
      = (∑ i ∈ Finset.range 47, stT32 (i+1)) + stT32 48 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 47
    simpa using h
  have hprev := st32_p47
  have hstep := st32_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p49 : ((1690672205147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT32 (i+1))
      = (∑ i ∈ Finset.range 48, stT32 (i+1)) + stT32 49 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 48
    simpa using h
  have hprev := st32_p48
  have hstep := st32_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p50 : ((1567410176069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT32 (i+1))
      = (∑ i ∈ Finset.range 49, stT32 (i+1)) + stT32 50 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 49
    simpa using h
  have hprev := st32_p49
  have hstep := st32_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p51 : ((1846681459157/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT32 (i+1))
      = (∑ i ∈ Finset.range 50, stT32 (i+1)) + stT32 51 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 50
    simpa using h
  have hprev := st32_p50
  have hstep := st32_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p52 : ((2083523382257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT32 (i+1))
      = (∑ i ∈ Finset.range 51, stT32 (i+1)) + stT32 52 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 51
    simpa using h
  have hprev := st32_p51
  have hstep := st32_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p53 : ((2194041992231/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT32 (i+1))
      = (∑ i ∈ Finset.range 52, stT32 (i+1)) + stT32 53 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 52
    simpa using h
  have hprev := st32_p52
  have hstep := st32_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p54 : ((10721064127603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT32 (i+1))
      = (∑ i ∈ Finset.range 53, stT32 (i+1)) + stT32 54 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 53
    simpa using h
  have hprev := st32_p53
  have hstep := st32_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p55 : ((9781124152403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT32 (i+1))
      = (∑ i ∈ Finset.range 54, stT32 (i+1)) + stT32 55 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 54
    simpa using h
  have hprev := st32_p54
  have hstep := st32_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p56 : ((264932123257/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT32 (i+1))
      = (∑ i ∈ Finset.range 55, stT32 (i+1)) + stT32 56 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 55
    simpa using h
  have hprev := st32_p55
  have hstep := st32_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p57 : ((903821687197/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT32 (i+1))
      = (∑ i ∈ Finset.range 56, stT32 (i+1)) + stT32 57 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 56
    simpa using h
  have hprev := st32_p56
  have hstep := st32_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p58 : ((6414255430791/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT32 (i+1))
      = (∑ i ∈ Finset.range 57, stT32 (i+1)) + stT32 58 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 57
    simpa using h
  have hprev := st32_p57
  have hstep := st32_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p59 : ((6253412128851/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT32 (i+1))
      = (∑ i ∈ Finset.range 58, stT32 (i+1)) + stT32 59 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 58
    simpa using h
  have hprev := st32_p58
  have hstep := st32_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p60 : ((6772700264417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT32 (i+1))
      = (∑ i ∈ Finset.range 59, stT32 (i+1)) + stT32 60 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 59
    simpa using h
  have hprev := st32_p59
  have hstep := st32_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p61 : ((7808834227313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT32 (i+1))
      = (∑ i ∈ Finset.range 60, stT32 (i+1)) + stT32 61 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 60
    simpa using h
  have hprev := st32_p60
  have hstep := st32_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p62 : ((907144001149/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT32 (i+1))
      = (∑ i ∈ Finset.range 61, stT32 (i+1)) + stT32 62 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 61
    simpa using h
  have hprev := st32_p61
  have hstep := st32_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p63 : ((10229581841097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT32 (i+1))
      = (∑ i ∈ Finset.range 62, stT32 (i+1)) + stT32 63 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 62
    simpa using h
  have hprev := st32_p62
  have hstep := st32_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p64 : ((10998228091097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT32 (i+1))
      = (∑ i ∈ Finset.range 63, stT32 (i+1)) + stT32 64 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 63
    simpa using h
  have hprev := st32_p63
  have hstep := st32_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p65 : ((11203376523509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT32 (i+1))
      = (∑ i ∈ Finset.range 64, stT32 (i+1)) + stT32 65 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 64
    simpa using h
  have hprev := st32_p64
  have hstep := st32_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p66 : ((5406683630167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT32 (i+1))
      = (∑ i ∈ Finset.range 65, stT32 (i+1)) + stT32 66 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 65
    simpa using h
  have hprev := st32_p65
  have hstep := st32_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p67 : ((1241736377543/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT32 (i+1))
      = (∑ i ∈ Finset.range 66, stT32 (i+1)) + stT32 67 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 66
    simpa using h
  have hprev := st32_p66
  have hstep := st32_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p68 : ((2193221674473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT32 (i+1))
      = (∑ i ∈ Finset.range 67, stT32 (i+1)) + stT32 68 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 67
    simpa using h
  have hprev := st32_p67
  have hstep := st32_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p69 : ((7587146979701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT32 (i+1))
      = (∑ i ∈ Finset.range 68, stT32 (i+1)) + stT32 69 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 68
    simpa using h
  have hprev := st32_p68
  have hstep := st32_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p70 : ((82805637211/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT32 (i+1))
      = (∑ i ∈ Finset.range 69, stT32 (i+1)) + stT32 70 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 69
    simpa using h
  have hprev := st32_p69
  have hstep := st32_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p71 : ((3036897404959/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT32 (i+1))
      = (∑ i ∈ Finset.range 70, stT32 (i+1)) + stT32 71 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 70
    simpa using h
  have hprev := st32_p70
  have hstep := st32_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p72 : ((3016318817671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT32 (i+1))
      = (∑ i ∈ Finset.range 71, stT32 (i+1)) + stT32 72 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 71
    simpa using h
  have hprev := st32_p71
  have hstep := st32_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p73 : ((259814525417/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT32 (i+1))
      = (∑ i ∈ Finset.range 72, stT32 (i+1)) + stT32 73 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 72
    simpa using h
  have hprev := st32_p72
  have hstep := st32_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p74 : ((7362398184977/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT32 (i+1))
      = (∑ i ∈ Finset.range 73, stT32 (i+1)) + stT32 74 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 73
    simpa using h
  have hprev := st32_p73
  have hstep := st32_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p75 : ((8465681703377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT32 (i+1))
      = (∑ i ∈ Finset.range 74, stT32 (i+1)) + stT32 75 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 74
    simpa using h
  have hprev := st32_p74
  have hstep := st32_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p76 : ((9603827406991/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT32 (i+1))
      = (∑ i ∈ Finset.range 75, stT32 (i+1)) + stT32 76 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 75
    simpa using h
  have hprev := st32_p75
  have hstep := st32_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p77 : ((2644896424529/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT32 (i+1))
      = (∑ i ∈ Finset.range 76, stT32 (i+1)) + stT32 77 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 76
    simpa using h
  have hprev := st32_p76
  have hstep := st32_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p78 : ((11232903865731/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT32 (i+1))
      = (∑ i ∈ Finset.range 77, stT32 (i+1)) + stT32 78 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 77
    simpa using h
  have hprev := st32_p77
  have hstep := st32_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p79 : ((2292916806189/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT32 (i+1))
      = (∑ i ∈ Finset.range 78, stT32 (i+1)) + stT32 79 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 78
    simpa using h
  have hprev := st32_p78
  have hstep := st32_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p80 : ((11247820717059/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT32 (i+1))
      = (∑ i ∈ Finset.range 79, stT32 (i+1)) + stT32 80 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 79
    simpa using h
  have hprev := st32_p79
  have hstep := st32_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p81 : ((425088053267/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT32 (i+1))
      = (∑ i ∈ Finset.range 80, stT32 (i+1)) + stT32 81 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 80
    simpa using h
  have hprev := st32_p80
  have hstep := st32_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p82 : ((9706811370107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT32 (i+1))
      = (∑ i ∈ Finset.range 81, stT32 (i+1)) + stT32 82 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 81
    simpa using h
  have hprev := st32_p81
  have hstep := st32_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p83 : ((345219647321/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT32 (i+1))
      = (∑ i ∈ Finset.range 82, stT32 (i+1)) + stT32 83 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 82
    simpa using h
  have hprev := st32_p82
  have hstep := st32_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p84 : ((1511615255893/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT32 (i+1))
      = (∑ i ∈ Finset.range 83, stT32 (i+1)) + stT32 84 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 83
    simpa using h
  have hprev := st32_p83
  have hstep := st32_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p85 : ((103773505661/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT32 (i+1))
      = (∑ i ∈ Finset.range 84, stT32 (i+1)) + stT32 85 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 84
    simpa using h
  have hprev := st32_p84
  have hstep := st32_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p86 : ((750523194513/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT32 (i+1))
      = (∑ i ∈ Finset.range 85, stT32 (i+1)) + stT32 86 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 85
    simpa using h
  have hprev := st32_p85
  have hstep := st32_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p87 : ((1145221678191/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT32 (i+1))
      = (∑ i ∈ Finset.range 86, stT32 (i+1)) + stT32 87 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 86
    simpa using h
  have hprev := st32_p86
  have hstep := st32_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p88 : ((1459020114611/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT32 (i+1))
      = (∑ i ∈ Finset.range 87, stT32 (i+1)) + stT32 88 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 87
    simpa using h
  have hprev := st32_p87
  have hstep := st32_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p89 : ((631133859337/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT32 (i+1))
      = (∑ i ∈ Finset.range 88, stT32 (i+1)) + stT32 89 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 88
    simpa using h
  have hprev := st32_p88
  have hstep := st32_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p90 : ((3541898619359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT32 (i+1))
      = (∑ i ∈ Finset.range 89, stT32 (i+1)) + stT32 90 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 89
    simpa using h
  have hprev := st32_p89
  have hstep := st32_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p91 : ((4025719423583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT32 (i+1))
      = (∑ i ∈ Finset.range 90, stT32 (i+1)) + stT32 91 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 90
    simpa using h
  have hprev := st32_p90
  have hstep := st32_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p92 : ((4546452860423/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT32 (i+1))
      = (∑ i ∈ Finset.range 91, stT32 (i+1)) + stT32 92 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 91
    simpa using h
  have hprev := st32_p91
  have hstep := st32_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p93 : ((5041590741217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT32 (i+1))
      = (∑ i ∈ Finset.range 92, stT32 (i+1)) + stT32 93 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 92
    simpa using h
  have hprev := st32_p92
  have hstep := st32_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p94 : ((10908418330271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT32 (i+1))
      = (∑ i ∈ Finset.range 93, stT32 (i+1)) + stT32 94 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 93
    simpa using h
  have hprev := st32_p93
  have hstep := st32_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p95 : ((11478253693317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT32 (i+1))
      = (∑ i ∈ Finset.range 94, stT32 (i+1)) + stT32 95 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 94
    simpa using h
  have hprev := st32_p94
  have hstep := st32_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p96 : ((11734494632997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT32 (i+1))
      = (∑ i ∈ Finset.range 95, stT32 (i+1)) + stT32 96 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 95
    simpa using h
  have hprev := st32_p95
  have hstep := st32_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p97 : ((11655551403747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT32 (i+1))
      = (∑ i ∈ Finset.range 96, stT32 (i+1)) + stT32 97 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 96
    simpa using h
  have hprev := st32_p96
  have hstep := st32_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p98 : ((2814141555643/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT32 (i+1))
      = (∑ i ∈ Finset.range 97, stT32 (i+1)) + stT32 98 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 97
    simpa using h
  have hprev := st32_p97
  have hstep := st32_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p99 : ((5292821025127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT32 (i+1))
      = (∑ i ∈ Finset.range 98, stT32 (i+1)) + stT32 99 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 98
    simpa using h
  have hprev := st32_p98
  have hstep := st32_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st32_p100 : ((4858470525127/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT32 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT32 (i+1))
      = (∑ i ∈ Finset.range 99, stT32 (i+1)) + stT32 100 := by
    have h := Finset.sum_range_succ (fun i => stT32 (i+1)) 99
    simpa using h
  have hprev := st32_p99
  have hstep := st32_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 32`.** -/
theorem station_32_sign : hardyG (((32:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 32 100 (by norm_num) (by norm_num)
    ((45783/200000 : ℚ) : ℝ)
  have hchain := st32_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT32 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((32:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((45783/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((32:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((32:ℕ)):ℝ)+1) * ((((32:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((182961/400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((4858470525127/5000000000000 : ℚ) : ℝ) - ((182961/400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((45783/200000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((32:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((45783/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((32:ℕ)):ℝ))).re
      - Real.sin ((45783/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((32:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((32:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((32:ℕ)):ℝ)
      = ((((32:ℕ)):ℝ) * (Real.log (((32:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((32:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_32
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
  have hθwin : |(((45783/200000 : ℚ) : ℝ) + ((2:ℤ)) * (2*Real.pi) - Real.pi) - theta (((32:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((32:ℕ)):ℝ))
    (φ := ((45783/200000 : ℚ) : ℝ) + ((2:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((45783/200000 : ℚ) : ℝ) + ((2:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((45783/200000 : ℚ)) : ℝ) - Real.pi) + ((2:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((45783/200000 : ℚ)) : ℝ) - Real.pi) 2).1,
    (cos_sin_shift ((((45783/200000 : ℚ)) : ℝ) - Real.pi) 2).2]
  exact cos_sin_flip ((45783/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_32_sign
end AxiomAudit
