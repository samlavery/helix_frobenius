import RequestProject.DVPSqrtTable

/-!
# Station `t = 86` of the extended Hardy ladder (rung-91)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT86 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((86 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((29/40000 : ℚ) : ℝ))

theorem st86_c1 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((1 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1813/10000000) (δ := 21/100000000) (ψ := 29/40000) 86 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t1 : ((19999/20000 : ℚ) : ℝ) ≤ stT86 1 := by
  have hc : ((19999/20000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19999/20000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((19999/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c2 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-39871/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7653161/10000000) (δ := 329/50000000) (ψ := 29/40000) 86 9
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t2 : ((-70486173591/100000000000 : ℚ) : ℝ) ≤ stT86 2 := by
  have hc : ((-39873/40000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70486173591/100000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-39873/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c3 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((486587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 29019/500000) (δ := 371/50000000) (ψ := 29/40000) 86 15
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t3 : ((702291670031/1250000000000 : ℚ) : ℝ) ≤ stT86 3 := by
  have hc : ((243281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((702291670031/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((243281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c4 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((493619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -399827/10000000) (δ := 21/4000000) (ψ := 29/40000) 86 19
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t4 : ((246797/500000 : ℚ) : ℝ) ≤ stT86 4 := by
  have hc : ((246797/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246797/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((246797/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c5 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((98369/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 226073/5000000) (δ := 393/50000000) (ψ := 29/40000) 86 22
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t5 : ((21994854357/50000000000 : ℚ) : ℝ) ≤ stT86 5 := by
  have hc : ((24591/25000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21994854357/50000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((24591/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c6 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-988387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7472609/10000000) (δ := 569/100000000) (ψ := 29/40000) 86 25
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t6 : ((-4035277249071/10000000000000 : ℚ) : ℝ) ≤ stT86 6 := by
  have hc : ((-988437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4035277249071/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-988437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c7 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-166281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5746139/10000000) (δ := 113/25000000) (ψ := 29/40000) 86 27
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t7 : ((-251412158323/1000000000000 : ℚ) : ℝ) ≤ stT86 7 := by
  have hc : ((-332587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251412158323/1000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-332587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c8 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-971449/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7255147/10000000) (δ := 521/100000000) (ψ := 29/40000) 86 28
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t8 : ((-1717383872733/5000000000000 : ℚ) : ℝ) ≤ stT86 8 := by
  have hc : ((-971499/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1717383872733/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-971499/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c9 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((55863/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1162573/10000000) (δ := 643/100000000) (ψ := 29/40000) 86 30
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t9 : ((1489596517707/5000000000000 : ℚ) : ℝ) ≤ stT86 9 := by
  have hc : ((446879/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1489596517707/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((446879/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c10 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-497439/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7600843/10000000) (δ := 191/25000000) (ψ := 29/40000) 86 32
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t10 : ((-98319966437/312500000000 : ℚ) : ℝ) ≤ stT86 10 := by
  have hc : ((-62183/62500 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-98319966437/312500000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-62183/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c11 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((429509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2817117/10000000) (δ := 123/20000000) (ψ := 29/40000) 86 33
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t11 : ((1294867413867/10000000000000 : ℚ) : ℝ) ≤ stT86 11 := by
  have hc : ((429459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1294867413867/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((429459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c12 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((997341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 91183/5000000) (δ := 437/100000000) (ψ := 29/40000) 86 34
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t12 : ((2878930791541/10000000000000 : ℚ) : ℝ) ≤ stT86 12 := by
  have hc : ((997291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2878930791541/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((997291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c13 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((156337/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13153/78125) (δ := 457/100000000) (ψ := 29/40000) 86 35
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t13 : ((867145869/4000000000 : ℚ) : ℝ) ≤ stT86 13 := by
  have hc : ((156327/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((867145869/4000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((156327/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c14 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((722397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 381767/2000000) (δ := 159/25000000) (ψ := 29/40000) 86 36
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t14 : ((482638315091/2500000000000 : ℚ) : ℝ) ≤ stT86 14 := by
  have hc : ((722347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482638315091/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((722347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c15 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((293/320 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1034339/10000000) (δ := 177/20000000) (ψ := 29/40000) 86 37
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t15 : ((23640036631/100000000000 : ℚ) : ℝ) ≤ stT86 15 := by
  have hc : ((36623/40000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23640036631/100000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((36623/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c16 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((949507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -398921/5000000) (δ := 347/50000000) (ψ := 29/40000) 86 38
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t16 : ((949457/4000000 : ℚ) : ℝ) ≤ stT86 16 := by
  have hc : ((949457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((949457/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((949457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c17 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((90593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3471511/10000000) (δ := 483/100000000) (ψ := 29/40000) 86 39
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t17 : ((6864363819/156250000000 : ℚ) : ℝ) ≤ stT86 17 := by
  have hc : ((11321/62500 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6864363819/156250000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((11321/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c18 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-463319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -430651/625000) (δ := 47/10000000) (ψ := 29/40000) 86 40
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t18 : ((-68257029057/312500000000 : ℚ) : ℝ) ≤ stT86 18 := by
  have hc : ((-28959/31250 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68257029057/312500000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-28959/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c19 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-317241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4734037/10000000) (δ := 67/10000000) (ψ := 29/40000) 86 40
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t19 : ((-363957842989/5000000000000 : ℚ) : ℝ) ≤ stT86 19 := by
  have hc : ((-317291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-363957842989/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-317291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c20 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((499883/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13533/2500000) (δ := 621/100000000) (ψ := 29/40000) 86 41
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t20 : ((558857989243/2500000000000 : ℚ) : ℝ) ≤ stT86 20 := by
  have hc : ((249929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((558857989243/2500000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((249929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c21 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-11871/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2581973/5000000) (δ := 551/100000000) (ψ := 29/40000) 86 42
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t21 : ((-103629498531/1000000000000 : ℚ) : ℝ) ≤ stT86 21 := by
  have hc : ((-47489/100000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-103629498531/1000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-47489/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c22 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-356339/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4837857/10000000) (δ := 27/6250000) (ψ := 29/40000) 86 42
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t22 : ((-94978024889/1250000000000 : ℚ) : ℝ) ≤ stT86 22 := by
  have hc : ((-356389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94978024889/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-356389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c23 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((216307/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1312977/10000000) (δ := 741/100000000) (ψ := 29/40000) 86 43
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t23 : ((112751294727/625000000000 : ℚ) : ℝ) ≤ stT86 23 := by
  have hc : ((432589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((112751294727/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((432589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c24 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-499989/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391867/500000) (δ := 621/100000000) (ψ := 29/40000) 86 43
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t24 : ((-255162394347/1250000000000 : ℚ) : ℝ) ≤ stT86 24 := by
  have hc : ((-250007/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-255162394347/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-250007/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c25 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((467517/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 453053/5000000) (δ := 13/2000000) (ψ := 29/40000) 86 44
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t25 : ((116873/625000 : ℚ) : ℝ) ≤ stT86 25 := by
  have hc : ((116873/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116873/625000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((116873/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c26 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-828803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1592351/2500000) (δ := 539/100000000) (ψ := 29/40000) 86 45
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t26 : ((-812757503593/5000000000000 : ℚ) : ℝ) ≤ stT86 26 := by
  have hc : ((-828853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-812757503593/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-828853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c27 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((766189/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 872383/5000000) (δ := 17/3125000) (ψ := 29/40000) 86 45
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t27 : ((2948869011/20000000000 : ℚ) : ℝ) ≤ stT86 27 := by
  have hc : ((766139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2948869011/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((766139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c28 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-155019/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3072077/5000000) (δ := 101/12500000) (ψ := 29/40000) 86 46
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t28 : ((-292977369867/2000000000000 : ℚ) : ℝ) ≤ stT86 28 := by
  have hc : ((-155029/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292977369867/2000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-155029/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c29 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((847153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8753/62500) (δ := 157/25000000) (ψ := 29/40000) 86 46
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t29 : ((1573030457159/10000000000000 : ℚ) : ℝ) ≤ stT86 29 := by
  have hc : ((847103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1573030457159/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((847103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c30 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-188939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140373/200000) (δ := 133/20000000) (ψ := 29/40000) 86 47
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t30 : ((-172486062579/1000000000000 : ℚ) : ℝ) ≤ stT86 30 := by
  have hc : ((-188949/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-172486062579/1000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-188949/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c31 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((499961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15581/5000000) (δ := 429/50000000) (ψ := 29/40000) 86 47
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t31 : ((28059736019/156250000000 : ℚ) : ℝ) ≤ stT86 31 := by
  have hc : ((15623/15625 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28059736019/156250000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((15623/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c32 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-921551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6857133/10000000) (δ := 419/50000000) (ψ := 29/40000) 86 47
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t32 : ((-1629175834967/10000000000000 : ℚ) : ℝ) ≤ stT86 32 := by
  have hc : ((-921601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1629175834967/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-921601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c33 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((313161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -558731/2500000) (δ := 129/25000000) (ψ := 29/40000) 86 48
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t33 : ((4258590887/39062500000 : ℚ) : ℝ) ≤ stT86 33 := by
  have hc : ((19571/31250 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4258590887/39062500000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((19571/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c34 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-102409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4183463/10000000) (δ := 667/100000000) (ψ := 29/40000) 86 48
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t34 : ((-87857875287/5000000000000 : ℚ) : ℝ) ≤ stT86 34 := by
  have hc : ((-102459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87857875287/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-102459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c35 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-259669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264609/500000) (δ := 507/100000000) (ψ := 29/40000) 86 49
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t35 : ((-219481552723/2500000000000 : ℚ) : ℝ) ≤ stT86 35 := by
  have hc : ((-129847/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219481552723/2500000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-129847/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c36 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((953599/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 764559/10000000) (δ := 67/12500000) (ψ := 29/40000) 86 49
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t36 : ((794623848817/5000000000000 : ℚ) : ℝ) ≤ stT86 36 := by
  have hc : ((953549/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((794623848817/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((953549/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c37 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-177449/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3327669/5000000) (δ := 97/12500000) (ψ := 29/40000) 86 49
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t37 : ((-29174082141/200000000000 : ℚ) : ℝ) ≤ stT86 37 := by
  have hc : ((-177459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29174082141/200000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-177459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c38 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((9633/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -414869/1250000) (δ := 497/100000000) (ψ := 29/40000) 86 50
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t38 : ((7811771517/200000000000 : ℚ) : ℝ) ≤ stT86 38 := by
  have hc : ((9631/40000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7811771517/200000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((9631/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c39 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((308327/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1132889/5000000) (δ := 233/50000000) (ψ := 29/40000) 86 50
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t39 : ((246839067431/2500000000000 : ℚ) : ℝ) ≤ stT86 39 := by
  have hc : ((154151/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246839067431/2500000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((154151/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c40 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-998321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3854553/5000000) (δ := 437/100000000) (ψ := 29/40000) 86 50
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t40 : ((-1578563324569/10000000000000 : ℚ) : ℝ) ≤ stT86 40 := by
  have hc : ((-998371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1578563324569/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-998371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c41 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((59359/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -537989/2000000) (δ := 71/12500000) (ψ := 29/40000) 86 51
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t41 : ((370773542907/5000000000000 : ℚ) : ℝ) ≤ stT86 41 := by
  have hc : ((237411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((370773542907/5000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((237411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c42 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((543319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 622757/2500000) (δ := 147/20000000) (ψ := 29/40000) 86 51
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t42 : ((838281994877/10000000000000 : ℚ) : ℝ) ≤ stT86 42 := by
  have hc : ((543269/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((838281994877/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((543269/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c43 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-992621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1510017/2000000) (δ := 151/20000000) (ψ := 29/40000) 86 51
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t43 : ((-756904688803/5000000000000 : ℚ) : ℝ) ≤ stT86 43 := by
  have hc : ((-992671/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-756904688803/5000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-992671/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c44 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((280911/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -803783/2500000) (δ := 151/25000000) (ψ := 29/40000) 86 52
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t44 : ((105853421429/2500000000000 : ℚ) : ℝ) ≤ stT86 44 := by
  have hc : ((280861/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105853421429/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((280861/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c45 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((798129/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 404133/2500000) (δ := 739/100000000) (ψ := 29/40000) 86 52
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t45 : ((1189705144169/10000000000000 : ℚ) : ℝ) ≤ stT86 45 := by
  have hc : ((798079/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1189705144169/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((798079/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c46 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-822619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6341997/10000000) (δ := 799/100000000) (ψ := 29/40000) 86 52
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t46 : ((-60647981349/500000000000 : ℚ) : ℝ) ≤ stT86 46 := by
  have hc : ((-822669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60647981349/500000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-822669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c47 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-32031/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1185533/2500000) (δ := 873/100000000) (ψ := 29/40000) 86 53
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t47 : ((-233646557/5000000000 : ℚ) : ℝ) ≤ stT86 47 := by
  have hc : ((-8009/25000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233646557/5000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-8009/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c48 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((498141/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215649/10000000) (δ := 793/100000000) (ψ := 29/40000) 86 53
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t48 : ((1437936363/10000000000 : ℚ) : ℝ) ≤ stT86 48 := by
  have hc : ((124529/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1437936363/10000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((124529/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c49 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-57971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2108749/5000000) (δ := 83/10000000) (ψ := 29/40000) 86 53
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t49 : ((-5178216357/312500000000 : ℚ) : ℝ) ≤ stT86 49 := by
  have hc : ((-14499/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5178216357/312500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-14499/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c50 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-960267/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7146883/10000000) (δ := 823/100000000) (ψ := 29/40000) 86 54
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t50 : ((-679046872919/5000000000000 : ℚ) : ℝ) ≤ stT86 50 := by
  have hc : ((-960317/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-679046872919/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-960317/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c51 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((403253/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1444659/5000000) (δ := 583/100000000) (ψ := 29/40000) 86 54
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t51 : ((14114927421/250000000000 : ℚ) : ℝ) ≤ stT86 51 := by
  have hc : ((403203/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14114927421/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((403203/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c52 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((870673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 128557/1000000) (δ := 723/100000000) (ψ := 29/40000) 86 54
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t52 : ((4829345781/40000000000 : ℚ) : ℝ) ≤ stT86 52 := by
  have hc : ((870623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4829345781/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((870623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c53 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-274671/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1345233/2500000) (δ := 763/100000000) (ψ := 29/40000) 86 54
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t53 : ((-23582754611/312500000000 : ℚ) : ℝ) ≤ stT86 53 := by
  have hc : ((-34337/62500 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23582754611/312500000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-34337/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c54 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-814863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6308223/10000000) (δ := 123/25000000) (ψ := 29/40000) 86 55
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t54 : ((-277239106991/2500000000000 : ℚ) : ℝ) ≤ stT86 54 := by
  have hc : ((-814913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-277239106991/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-814913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c55 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((58553/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1181579/5000000) (δ := 711/100000000) (ψ := 29/40000) 86 55
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t55 : ((19736516163/250000000000 : ℚ) : ℝ) ≤ stT86 55 := by
  have hc : ((14637/25000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19736516163/250000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((14637/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c56 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((205721/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1510821/10000000) (δ := 771/100000000) (ψ := 29/40000) 86 55
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t56 : ((274889502801/2500000000000 : ℚ) : ℝ) ≤ stT86 56 := by
  have hc : ((411417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274889502801/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((411417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c57 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-263767/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 531623/1000000) (δ := 571/100000000) (ψ := 29/40000) 86 55
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t57 : ((-21837575571/312500000000 : ℚ) : ℝ) ≤ stT86 57 := by
  have hc : ((-16487/31250 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21837575571/312500000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-16487/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c58 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-886723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6652509/10000000) (δ := 801/100000000) (ψ := 29/40000) 86 56
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t58 : ((-232878117849/2000000000000 : ℚ) : ℝ) ≤ stT86 58 := by
  have hc : ((-886773/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-232878117849/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-886773/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c59 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((370841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1488603/5000000) (δ := 521/100000000) (ψ := 29/40000) 86 56
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t59 : ((482728724199/10000000000000 : ℚ) : ℝ) ≤ stT86 59 := by
  have hc : ((370791/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((482728724199/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((370791/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c60 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((483891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25453/400000) (δ := 261/50000000) (ψ := 29/40000) 86 56
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t60 : ((156167025701/1250000000000 : ℚ) : ℝ) ≤ stT86 60 := by
  have hc : ((241933/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156167025701/1250000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((241933/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c61 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-105059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33521/80000) (δ := 271/50000000) (ψ := 29/40000) 86 56
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t61 : ((-134578305221/10000000000000 : ℚ) : ℝ) ≤ stT86 61 := by
  have hc : ((-105109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134578305221/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-105109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c62 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-997747/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7686137/10000000) (δ := 361/50000000) (ψ := 29/40000) 86 56
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t62 : ((-633602092797/5000000000000 : ℚ) : ℝ) ≤ stT86 62 := by
  have hc : ((-997797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-633602092797/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-997797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c63 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-258921/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4581753/10000000) (δ := 651/100000000) (ψ := 29/40000) 86 57
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t63 : ((-163136450711/5000000000000 : ℚ) : ℝ) ≤ stT86 63 := by
  have hc : ((-258971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163136450711/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-258971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c64 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((887759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74741/625000) (δ := 89/12500000) (ψ := 29/40000) 86 57
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t64 : ((887709/8000000 : ℚ) : ℝ) ≤ stT86 64 := by
  have hc : ((887709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((887709/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((887709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c65 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((131241/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 267193/1250000) (δ := 37/6250000) (ψ := 29/40000) 86 57
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t65 : ((162771977157/2000000000000 : ℚ) : ℝ) ≤ stT86 65 := by
  have hc : ((131231/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((162771977157/2000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((131231/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c66 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-562349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 108401/200000) (δ := 531/100000000) (ψ := 29/40000) 86 57
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t66 : ((-138453073017/2000000000000 : ℚ) : ℝ) ≤ stT86 66 := by
  have hc : ((-562399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-138453073017/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-562399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c67 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-474667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7054769/10000000) (δ := 7/1000000) (ψ := 29/40000) 86 58
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t67 : ((-28996442147/250000000000 : ℚ) : ℝ) ≤ stT86 67 := by
  have hc : ((-118673/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28996442147/250000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-118673/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c68 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((2873/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1934763/5000000) (δ := 21/2500000) (ψ := 29/40000) 86 58
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t68 : ((6952889313/2500000000000 : ℚ) : ℝ) ≤ stT86 68 := by
  have hc : ((11467/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6952889313/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((11467/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c69 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((47879/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -22837/312500) (δ := 21/2500000) (ψ := 29/40000) 86 58
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t69 : ((57636507537/500000000000 : ℚ) : ℝ) ≤ stT86 69 := by
  have hc : ((95753/100000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57636507537/500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((95753/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c70 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((36603/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1181397/5000000) (δ := 27/5000000) (ψ := 29/40000) 86 58
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t70 : ((87490390793/1250000000000 : ℚ) : ℝ) ≤ stT86 70 := by
  have hc : ((292799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87490390793/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((292799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c71 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-279923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5412491/10000000) (δ := 643/100000000) (ψ := 29/40000) 86 58
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t71 : ((-41529655917/625000000000 : ℚ) : ℝ) ≤ stT86 71 := by
  have hc : ((-69987/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41529655917/625000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-69987/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c72 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-974521/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -728843/1000000) (δ := 709/100000000) (ψ := 29/40000) 86 59
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t72 : ((-71783976147/625000000000 : ℚ) : ℝ) ≤ stT86 72 := by
  have hc : ((-974571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71783976147/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-974571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c73 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-157689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2161433/5000000) (δ := 529/100000000) (ψ := 29/40000) 86 59
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t73 : ((-46154904617/2500000000000 : ℚ) : ℝ) ≤ stT86 73 := by
  have hc : ((-157739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46154904617/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-157739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c74 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((423877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1397651/10000000) (δ := 387/50000000) (ψ := 29/40000) 86 59
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t74 : ((30794861097/312500000000 : ℚ) : ℝ) ≤ stT86 74 := by
  have hc : ((105963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30794861097/312500000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((105963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c75 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((827969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1488299/10000000) (δ := 749/100000000) (ψ := 29/40000) 86 59
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t75 : ((9559980693/100000000000 : ℚ) : ℝ) ≤ stT86 75 := by
  have hc : ((827919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9559980693/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((827919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c76 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-162883/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2168011/5000000) (δ := 549/100000000) (ψ := 29/40000) 86 59
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t76 : ((-186897022707/10000000000000 : ℚ) : ℝ) ≤ stT86 76 := by
  have hc : ((-162933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-186897022707/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-162933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c77 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-480113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 178663/250000) (δ := 689/100000000) (ψ := 29/40000) 86 59
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t77 : ((-136792036407/1250000000000 : ℚ) : ℝ) ≤ stT86 77 := by
  have hc : ((-240069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136792036407/1250000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-240069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c78 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-677301/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5787211/10000000) (δ := 319/50000000) (ψ := 29/40000) 86 60
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t78 : ((-383474817789/5000000000000 : ℚ) : ℝ) ≤ stT86 78 := by
  have hc : ((-677351/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-383474817789/5000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-677351/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c79 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((86069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3048321/10000000) (δ := 219/50000000) (ψ := 29/40000) 86 60
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t79 : ((193642098831/5000000000000 : ℚ) : ℝ) ≤ stT86 79 := by
  have hc : ((172113/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193642098831/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((172113/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c80 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((495277/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343883/10000000) (δ := 299/50000000) (ψ := 29/40000) 86 60
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t80 : ((138427019829/1250000000000 : ℚ) : ℝ) ≤ stT86 80 := by
  have hc : ((123813/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138427019829/1250000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((123813/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c81 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((298603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2326959/10000000) (δ := 89/20000000) (ψ := 29/40000) 86 60
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t81 : ((165876650079/2500000000000 : ℚ) : ℝ) ≤ stT86 81 := by
  have hc : ((149289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165876650079/2500000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((149289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c82 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-403387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4965029/10000000) (δ := 239/50000000) (ψ := 29/40000) 86 60
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t82 : ((-111380483523/2500000000000 : ℚ) : ℝ) ≤ stT86 82 := by
  have hc : ((-403437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111380483523/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-403437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c83 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-496803/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3785561/5000000) (δ := 399/50000000) (ψ := 29/40000) 86 60
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t83 : ((-136334944101/1250000000000 : ℚ) : ℝ) ≤ stT86 83 := by
  have hc : ((-124207/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-136334944101/1250000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-124207/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c84 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-152089/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5561961/10000000) (δ := 227/25000000) (ψ := 29/40000) 86 61
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t84 : ((-33191285127/500000000000 : ℚ) : ℝ) ≤ stT86 84 := by
  have hc : ((-304203/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33191285127/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-304203/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c85 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((71161/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -188597/625000) (δ := 19/4000000) (ψ := 29/40000) 86 61
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t85 : ((19293518613/500000000000 : ℚ) : ℝ) ≤ stT86 85 := by
  have hc : ((71151/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19293518613/500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((71151/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c86 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((195967/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -62863/1250000) (δ := 159/20000000) (ψ := 29/40000) 86 61
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t86 : ((211305723939/2000000000000 : ℚ) : ℝ) ≤ stT86 86 := by
  have hc : ((195957/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((211305723939/2000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((195957/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c87 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((350831/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1982673/10000000) (δ := 91/12500000) (ψ := 29/40000) 86 61
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t87 : ((11753228821/156250000000 : ℚ) : ℝ) ≤ stT86 87 := by
  have hc : ((175403/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11753228821/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((175403/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c88 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-40741/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4439843/10000000) (δ := 187/25000000) (ψ := 29/40000) 86 61
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t88 : ((-10860182251/500000000000 : ℚ) : ℝ) ≤ stT86 88 := by
  have hc : ((-40751/200000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10860182251/500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-40751/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c89 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-461711/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6869247/10000000) (δ := 23/4000000) (ψ := 29/40000) 86 61
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t89 : ((-30589952283/312500000000 : ℚ) : ℝ) ≤ stT86 89 := by
  have hc : ((-57717/62500 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30589952283/312500000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-57717/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c90 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-843511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -804557/1250000) (δ := 303/50000000) (ψ := 29/40000) 86 62
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t90 : ((-889191745173/10000000000000 : ℚ) : ℝ) ≤ stT86 90 := by
  have hc : ((-843561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-889191745173/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-843561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c91 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-2139/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2030371/5000000) (δ := 443/50000000) (ψ := 29/40000) 86 62
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t91 : ((-448875637/80000000000 : ℚ) : ℝ) ≤ stT86 91 := by
  have hc : ((-2141/40000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-448875637/80000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-2141/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c92 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((774801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -106937/625000) (δ := 313/50000000) (ψ := 29/40000) 86 62
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t92 : ((201933424893/2500000000000 : ℚ) : ℝ) ≤ stT86 92 := by
  have hc : ((774751/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201933424893/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((774751/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c93 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((485027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 122671/2000000) (δ := 383/50000000) (ψ := 29/40000) 86 62
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t93 : ((251461654451/2500000000000 : ℚ) : ℝ) ≤ stT86 93 := by
  have hc : ((242501/250000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251461654451/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((242501/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c94 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((6166/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2912843/10000000) (δ := 353/50000000) (ψ := 29/40000) 86 62
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t94 : ((203485954827/5000000000000 : ℚ) : ℝ) ≤ stT86 94 := by
  have hc : ((197287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((203485954827/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((197287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c95 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-120821/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1296999/2500000) (δ := 383/50000000) (ψ := 29/40000) 86 62
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t95 : ((-247945266993/5000000000000 : ℚ) : ℝ) ≤ stT86 95 := by
  have hc : ((-241667/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-247945266993/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-241667/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c96 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-246569/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3719663/5000000) (δ := 393/50000000) (ψ := 29/40000) 86 62
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t96 : ((-503332514223/5000000000000 : ℚ) : ℝ) ≤ stT86 96 := by
  have hc : ((-493163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503332514223/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-493163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c97 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((-187069/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6040639/10000000) (δ := 637/100000000) (ψ := 29/40000) 86 63
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t97 : ((-379905279561/5000000000000 : ℚ) : ℝ) ≤ stT86 97 := by
  have hc : ((-374163/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379905279561/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-374163/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c98 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((2287/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3835491/10000000) (δ := 657/100000000) (ψ := 29/40000) 86 63
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t98 : ((2307060899/625000000000 : ℚ) : ℝ) ≤ stT86 98 := by
  have hc : ((18271/500000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2307060899/625000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((18271/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c99 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((394661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1652731/10000000) (δ := 223/50000000) (ψ := 29/40000) 86 63
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t99 : ((99155945383/1250000000000 : ℚ) : ℝ) ≤ stT86 99 := by
  have hc : ((98659/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99155945383/1250000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((98659/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_c100 :
    |Real.cos (((86 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((29/40000 : ℚ) : ℝ))
      - ((489709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 508091/10000000) (δ := 717/100000000) (ψ := 29/40000) 86 63
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st86_t100 : ((122420877579/1250000000000 : ℚ) : ℝ) ≤ stT86 100 := by
  have hc : ((122421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((86 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((29/40000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st86_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122420877579/1250000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((122421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st86_p1 : ((19999/20000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT86 (i+1) := by
  rw [Finset.sum_range_one]
  exact st86_t1

theorem st86_p2 : ((29508826409/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT86 (i+1))
      = (∑ i ∈ Finset.range 1, stT86 (i+1)) + stT86 2 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 1
    simpa using h
  have hprev := st86_p1
  have hstep := st86_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p3 : ((2142304000287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT86 (i+1))
      = (∑ i ∈ Finset.range 2, stT86 (i+1)) + stT86 3 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 2
    simpa using h
  have hprev := st86_p2
  have hstep := st86_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p4 : ((3376289000287/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT86 (i+1))
      = (∑ i ∈ Finset.range 3, stT86 (i+1)) + stT86 4 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 3
    simpa using h
  have hprev := st86_p3
  have hstep := st86_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p5 : ((4476031718137/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT86 (i+1))
      = (∑ i ∈ Finset.range 4, stT86 (i+1)) + stT86 5 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 4
    simpa using h
  have hprev := st86_p4
  have hstep := st86_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p6 : ((13868849623477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT86 (i+1))
      = (∑ i ∈ Finset.range 5, stT86 (i+1)) + stT86 6 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 5
    simpa using h
  have hprev := st86_p5
  have hstep := st86_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p7 : ((11354728040247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT86 (i+1))
      = (∑ i ∈ Finset.range 6, stT86 (i+1)) + stT86 7 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 6
    simpa using h
  have hprev := st86_p6
  have hstep := st86_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p8 : ((7919960294781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT86 (i+1))
      = (∑ i ∈ Finset.range 7, stT86 (i+1)) + stT86 8 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 7
    simpa using h
  have hprev := st86_p7
  have hstep := st86_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p9 : ((2179830666039/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT86 (i+1))
      = (∑ i ∈ Finset.range 8, stT86 (i+1)) + stT86 9 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 8
    simpa using h
  have hprev := st86_p8
  have hstep := st86_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p10 : ((7752914404211/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT86 (i+1))
      = (∑ i ∈ Finset.range 9, stT86 (i+1)) + stT86 10 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 9
    simpa using h
  have hprev := st86_p9
  have hstep := st86_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p11 : ((4523890909039/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT86 (i+1))
      = (∑ i ∈ Finset.range 10, stT86 (i+1)) + stT86 11 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 10
    simpa using h
  have hprev := st86_p10
  have hstep := st86_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p12 : ((11926712609619/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT86 (i+1))
      = (∑ i ∈ Finset.range 11, stT86 (i+1)) + stT86 12 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 11
    simpa using h
  have hprev := st86_p11
  have hstep := st86_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p13 : ((14094577282119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT86 (i+1))
      = (∑ i ∈ Finset.range 12, stT86 (i+1)) + stT86 13 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 12
    simpa using h
  have hprev := st86_p12
  have hstep := st86_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p14 : ((16025130542483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT86 (i+1))
      = (∑ i ∈ Finset.range 13, stT86 (i+1)) + stT86 14 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 13
    simpa using h
  have hprev := st86_p13
  have hstep := st86_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p15 : ((18389134205583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT86 (i+1))
      = (∑ i ∈ Finset.range 14, stT86 (i+1)) + stT86 15 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 14
    simpa using h
  have hprev := st86_p14
  have hstep := st86_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p16 : ((20762776705583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT86 (i+1))
      = (∑ i ∈ Finset.range 15, stT86 (i+1)) + stT86 16 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 15
    simpa using h
  have hprev := st86_p15
  have hstep := st86_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p17 : ((21202095989999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT86 (i+1))
      = (∑ i ∈ Finset.range 16, stT86 (i+1)) + stT86 17 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 16
    simpa using h
  have hprev := st86_p16
  have hstep := st86_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p18 : ((760714842407/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT86 (i+1))
      = (∑ i ∈ Finset.range 17, stT86 (i+1)) + stT86 18 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 17
    simpa using h
  have hprev := st86_p17
  have hstep := st86_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p19 : ((18289955374197/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT86 (i+1))
      = (∑ i ∈ Finset.range 18, stT86 (i+1)) + stT86 19 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 18
    simpa using h
  have hprev := st86_p18
  have hstep := st86_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p20 : ((20525387331169/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT86 (i+1))
      = (∑ i ∈ Finset.range 19, stT86 (i+1)) + stT86 20 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 19
    simpa using h
  have hprev := st86_p19
  have hstep := st86_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p21 : ((19489092345859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT86 (i+1))
      = (∑ i ∈ Finset.range 20, stT86 (i+1)) + stT86 21 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 20
    simpa using h
  have hprev := st86_p20
  have hstep := st86_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p22 : ((18729268146747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT86 (i+1))
      = (∑ i ∈ Finset.range 21, stT86 (i+1)) + stT86 22 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 21
    simpa using h
  have hprev := st86_p21
  have hstep := st86_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p23 : ((20533288862379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT86 (i+1))
      = (∑ i ∈ Finset.range 22, stT86 (i+1)) + stT86 23 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 22
    simpa using h
  have hprev := st86_p22
  have hstep := st86_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p24 : ((18491989707603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT86 (i+1))
      = (∑ i ∈ Finset.range 23, stT86 (i+1)) + stT86 24 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 23
    simpa using h
  have hprev := st86_p23
  have hstep := st86_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p25 : ((20361957707603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT86 (i+1))
      = (∑ i ∈ Finset.range 24, stT86 (i+1)) + stT86 25 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 24
    simpa using h
  have hprev := st86_p24
  have hstep := st86_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p26 : ((18736442700417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT86 (i+1))
      = (∑ i ∈ Finset.range 25, stT86 (i+1)) + stT86 26 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 25
    simpa using h
  have hprev := st86_p25
  have hstep := st86_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p27 : ((20210877205917/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT86 (i+1))
      = (∑ i ∈ Finset.range 26, stT86 (i+1)) + stT86 27 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 26
    simpa using h
  have hprev := st86_p26
  have hstep := st86_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p28 : ((9372995178291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT86 (i+1))
      = (∑ i ∈ Finset.range 27, stT86 (i+1)) + stT86 28 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 27
    simpa using h
  have hprev := st86_p27
  have hstep := st86_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p29 : ((20319020813741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT86 (i+1))
      = (∑ i ∈ Finset.range 28, stT86 (i+1)) + stT86 29 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 28
    simpa using h
  have hprev := st86_p28
  have hstep := st86_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p30 : ((18594160187951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT86 (i+1))
      = (∑ i ∈ Finset.range 29, stT86 (i+1)) + stT86 30 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 29
    simpa using h
  have hprev := st86_p29
  have hstep := st86_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p31 : ((20389983293167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT86 (i+1))
      = (∑ i ∈ Finset.range 30, stT86 (i+1)) + stT86 31 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 30
    simpa using h
  have hprev := st86_p30
  have hstep := st86_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p32 : ((93804037291/50000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT86 (i+1))
      = (∑ i ∈ Finset.range 31, stT86 (i+1)) + stT86 32 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 31
    simpa using h
  have hprev := st86_p31
  have hstep := st86_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p33 : ((2481375840659/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT86 (i+1))
      = (∑ i ∈ Finset.range 32, stT86 (i+1)) + stT86 33 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 32
    simpa using h
  have hprev := st86_p32
  have hstep := st86_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p34 : ((9837645487349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT86 (i+1))
      = (∑ i ∈ Finset.range 33, stT86 (i+1)) + stT86 34 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 33
    simpa using h
  have hprev := st86_p33
  have hstep := st86_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p35 : ((9398682381903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT86 (i+1))
      = (∑ i ∈ Finset.range 34, stT86 (i+1)) + stT86 35 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 34
    simpa using h
  have hprev := st86_p34
  have hstep := st86_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p36 : ((31854081971/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT86 (i+1))
      = (∑ i ∈ Finset.range 35, stT86 (i+1)) + stT86 36 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 35
    simpa using h
  have hprev := st86_p35
  have hstep := st86_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p37 : ((1892790835439/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT86 (i+1))
      = (∑ i ∈ Finset.range 36, stT86 (i+1)) + stT86 37 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 36
    simpa using h
  have hprev := st86_p36
  have hstep := st86_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p38 : ((60370302907/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT86 (i+1))
      = (∑ i ∈ Finset.range 37, stT86 (i+1)) + stT86 38 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 37
    simpa using h
  have hprev := st86_p37
  have hstep := st86_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p39 : ((5076463299991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT86 (i+1))
      = (∑ i ∈ Finset.range 38, stT86 (i+1)) + stT86 39 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 38
    simpa using h
  have hprev := st86_p38
  have hstep := st86_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p40 : ((3745457975079/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT86 (i+1))
      = (∑ i ∈ Finset.range 39, stT86 (i+1)) + stT86 40 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 39
    simpa using h
  have hprev := st86_p39
  have hstep := st86_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p41 : ((19468836961209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT86 (i+1))
      = (∑ i ∈ Finset.range 40, stT86 (i+1)) + stT86 41 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 40
    simpa using h
  have hprev := st86_p40
  have hstep := st86_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p42 : ((10153559478043/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT86 (i+1))
      = (∑ i ∈ Finset.range 41, stT86 (i+1)) + stT86 42 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 41
    simpa using h
  have hprev := st86_p41
  have hstep := st86_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p43 : ((234916369731/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT86 (i+1))
      = (∑ i ∈ Finset.range 42, stT86 (i+1)) + stT86 43 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 42
    simpa using h
  have hprev := st86_p42
  have hstep := st86_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p44 : ((4804180816049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT86 (i+1))
      = (∑ i ∈ Finset.range 43, stT86 (i+1)) + stT86 44 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 43
    simpa using h
  have hprev := st86_p43
  have hstep := st86_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p45 : ((4081285681673/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT86 (i+1))
      = (∑ i ∈ Finset.range 44, stT86 (i+1)) + stT86 45 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 44
    simpa using h
  have hprev := st86_p44
  have hstep := st86_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p46 : ((3838693756277/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT86 (i+1))
      = (∑ i ∈ Finset.range 45, stT86 (i+1)) + stT86 46 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 45
    simpa using h
  have hprev := st86_p45
  have hstep := st86_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p47 : ((3745235133477/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT86 (i+1))
      = (∑ i ∈ Finset.range 46, stT86 (i+1)) + stT86 47 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 46
    simpa using h
  have hprev := st86_p46
  have hstep := st86_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p48 : ((4032822406077/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT86 (i+1))
      = (∑ i ∈ Finset.range 47, stT86 (i+1)) + stT86 48 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 47
    simpa using h
  have hprev := st86_p47
  have hstep := st86_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p49 : ((19998409106961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT86 (i+1))
      = (∑ i ∈ Finset.range 48, stT86 (i+1)) + stT86 49 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 48
    simpa using h
  have hprev := st86_p48
  have hstep := st86_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p50 : ((18640315361123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT86 (i+1))
      = (∑ i ∈ Finset.range 49, stT86 (i+1)) + stT86 50 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 49
    simpa using h
  have hprev := st86_p49
  have hstep := st86_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p51 : ((19204912457963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT86 (i+1))
      = (∑ i ∈ Finset.range 50, stT86 (i+1)) + stT86 51 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 50
    simpa using h
  have hprev := st86_p50
  have hstep := st86_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p52 : ((20412248903213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT86 (i+1))
      = (∑ i ∈ Finset.range 51, stT86 (i+1)) + stT86 52 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 51
    simpa using h
  have hprev := st86_p51
  have hstep := st86_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p53 : ((19657600755661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT86 (i+1))
      = (∑ i ∈ Finset.range 52, stT86 (i+1)) + stT86 53 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 52
    simpa using h
  have hprev := st86_p52
  have hstep := st86_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p54 : ((18548644327697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT86 (i+1))
      = (∑ i ∈ Finset.range 53, stT86 (i+1)) + stT86 54 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 53
    simpa using h
  have hprev := st86_p53
  have hstep := st86_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p55 : ((19338104974217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT86 (i+1))
      = (∑ i ∈ Finset.range 54, stT86 (i+1)) + stT86 55 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 54
    simpa using h
  have hprev := st86_p54
  have hstep := st86_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p56 : ((20437662985421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT86 (i+1))
      = (∑ i ∈ Finset.range 55, stT86 (i+1)) + stT86 56 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 55
    simpa using h
  have hprev := st86_p55
  have hstep := st86_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p57 : ((19738860567149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT86 (i+1))
      = (∑ i ∈ Finset.range 56, stT86 (i+1)) + stT86 57 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 56
    simpa using h
  have hprev := st86_p56
  have hstep := st86_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p58 : ((1160904373619/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT86 (i+1))
      = (∑ i ∈ Finset.range 57, stT86 (i+1)) + stT86 58 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 57
    simpa using h
  have hprev := st86_p57
  have hstep := st86_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p59 : ((19057198702103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT86 (i+1))
      = (∑ i ∈ Finset.range 58, stT86 (i+1)) + stT86 59 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 58
    simpa using h
  have hprev := st86_p58
  have hstep := st86_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p60 : ((20306534907711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT86 (i+1))
      = (∑ i ∈ Finset.range 59, stT86 (i+1)) + stT86 60 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 59
    simpa using h
  have hprev := st86_p59
  have hstep := st86_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p61 : ((2017195660249/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT86 (i+1))
      = (∑ i ∈ Finset.range 60, stT86 (i+1)) + stT86 61 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 60
    simpa using h
  have hprev := st86_p60
  have hstep := st86_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p62 : ((147693378257/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT86 (i+1))
      = (∑ i ∈ Finset.range 61, stT86 (i+1)) + stT86 62 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 61
    simpa using h
  have hprev := st86_p61
  have hstep := st86_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p63 : ((9289239757737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT86 (i+1))
      = (∑ i ∈ Finset.range 62, stT86 (i+1)) + stT86 63 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 62
    simpa using h
  have hprev := st86_p62
  have hstep := st86_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p64 : ((9844057882737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT86 (i+1))
      = (∑ i ∈ Finset.range 63, stT86 (i+1)) + stT86 64 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 63
    simpa using h
  have hprev := st86_p63
  have hstep := st86_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p65 : ((20501975651259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT86 (i+1))
      = (∑ i ∈ Finset.range 64, stT86 (i+1)) + stT86 65 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 64
    simpa using h
  have hprev := st86_p64
  have hstep := st86_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p66 : ((9904855143087/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT86 (i+1))
      = (∑ i ∈ Finset.range 65, stT86 (i+1)) + stT86 66 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 65
    simpa using h
  have hprev := st86_p65
  have hstep := st86_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p67 : ((9324926300147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT86 (i+1))
      = (∑ i ∈ Finset.range 66, stT86 (i+1)) + stT86 67 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 66
    simpa using h
  have hprev := st86_p66
  have hstep := st86_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p68 : ((9338832078773/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT86 (i+1))
      = (∑ i ∈ Finset.range 67, stT86 (i+1)) + stT86 68 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 67
    simpa using h
  have hprev := st86_p67
  have hstep := st86_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p69 : ((9915197154143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT86 (i+1))
      = (∑ i ∈ Finset.range 68, stT86 (i+1)) + stT86 69 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 68
    simpa using h
  have hprev := st86_p68
  have hstep := st86_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p70 : ((2053031743463/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT86 (i+1))
      = (∑ i ∈ Finset.range 69, stT86 (i+1)) + stT86 70 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 69
    simpa using h
  have hprev := st86_p69
  have hstep := st86_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p71 : ((9932921469979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT86 (i+1))
      = (∑ i ∈ Finset.range 70, stT86 (i+1)) + stT86 71 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 70
    simpa using h
  have hprev := st86_p70
  have hstep := st86_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p72 : ((9358649660803/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT86 (i+1))
      = (∑ i ∈ Finset.range 71, stT86 (i+1)) + stT86 72 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 71
    simpa using h
  have hprev := st86_p71
  have hstep := st86_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p73 : ((9266339851569/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT86 (i+1))
      = (∑ i ∈ Finset.range 72, stT86 (i+1)) + stT86 73 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 72
    simpa using h
  have hprev := st86_p72
  have hstep := st86_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p74 : ((9759057629121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT86 (i+1))
      = (∑ i ∈ Finset.range 73, stT86 (i+1)) + stT86 74 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 73
    simpa using h
  have hprev := st86_p73
  have hstep := st86_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p75 : ((10237056663771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT86 (i+1))
      = (∑ i ∈ Finset.range 74, stT86 (i+1)) + stT86 75 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 74
    simpa using h
  have hprev := st86_p74
  have hstep := st86_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p76 : ((4057443260967/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT86 (i+1))
      = (∑ i ∈ Finset.range 75, stT86 (i+1)) + stT86 76 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 75
    simpa using h
  have hprev := st86_p75
  have hstep := st86_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p77 : ((19192880013579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT86 (i+1))
      = (∑ i ∈ Finset.range 76, stT86 (i+1)) + stT86 77 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 76
    simpa using h
  have hprev := st86_p76
  have hstep := st86_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p78 : ((18425930378001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT86 (i+1))
      = (∑ i ∈ Finset.range 77, stT86 (i+1)) + stT86 78 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 77
    simpa using h
  have hprev := st86_p77
  have hstep := st86_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p79 : ((18813214575663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT86 (i+1))
      = (∑ i ∈ Finset.range 78, stT86 (i+1)) + stT86 79 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 78
    simpa using h
  have hprev := st86_p78
  have hstep := st86_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p80 : ((3984126146859/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT86 (i+1))
      = (∑ i ∈ Finset.range 79, stT86 (i+1)) + stT86 80 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 79
    simpa using h
  have hprev := st86_p79
  have hstep := st86_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p81 : ((20584137334611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT86 (i+1))
      = (∑ i ∈ Finset.range 80, stT86 (i+1)) + stT86 81 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 80
    simpa using h
  have hprev := st86_p80
  have hstep := st86_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p82 : ((20138615400519/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT86 (i+1))
      = (∑ i ∈ Finset.range 81, stT86 (i+1)) + stT86 82 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 81
    simpa using h
  have hprev := st86_p81
  have hstep := st86_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p83 : ((19047935847711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT86 (i+1))
      = (∑ i ∈ Finset.range 82, stT86 (i+1)) + stT86 83 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 82
    simpa using h
  have hprev := st86_p82
  have hstep := st86_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p84 : ((18384110145171/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT86 (i+1))
      = (∑ i ∈ Finset.range 83, stT86 (i+1)) + stT86 84 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 83
    simpa using h
  have hprev := st86_p83
  have hstep := st86_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p85 : ((18769980517431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT86 (i+1))
      = (∑ i ∈ Finset.range 84, stT86 (i+1)) + stT86 85 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 84
    simpa using h
  have hprev := st86_p84
  have hstep := st86_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p86 : ((9913254568563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT86 (i+1))
      = (∑ i ∈ Finset.range 85, stT86 (i+1)) + stT86 86 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 85
    simpa using h
  have hprev := st86_p85
  have hstep := st86_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p87 : ((2057871578167/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT86 (i+1))
      = (∑ i ∈ Finset.range 86, stT86 (i+1)) + stT86 87 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 86
    simpa using h
  have hprev := st86_p86
  have hstep := st86_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p88 : ((407230242733/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT86 (i+1))
      = (∑ i ∈ Finset.range 87, stT86 (i+1)) + stT86 88 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 87
    simpa using h
  have hprev := st86_p87
  have hstep := st86_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p89 : ((9691316831797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT86 (i+1))
      = (∑ i ∈ Finset.range 88, stT86 (i+1)) + stT86 89 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 88
    simpa using h
  have hprev := st86_p88
  have hstep := st86_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p90 : ((18493441918421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT86 (i+1))
      = (∑ i ∈ Finset.range 89, stT86 (i+1)) + stT86 90 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 89
    simpa using h
  have hprev := st86_p89
  have hstep := st86_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p91 : ((4609333115949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT86 (i+1))
      = (∑ i ∈ Finset.range 90, stT86 (i+1)) + stT86 91 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 90
    simpa using h
  have hprev := st86_p90
  have hstep := st86_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p92 : ((2405633270421/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT86 (i+1))
      = (∑ i ∈ Finset.range 91, stT86 (i+1)) + stT86 92 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 91
    simpa using h
  have hprev := st86_p91
  have hstep := st86_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p93 : ((5062728195293/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT86 (i+1))
      = (∑ i ∈ Finset.range 92, stT86 (i+1)) + stT86 93 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 92
    simpa using h
  have hprev := st86_p92
  have hstep := st86_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p94 : ((10328942345413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT86 (i+1))
      = (∑ i ∈ Finset.range 93, stT86 (i+1)) + stT86 94 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 93
    simpa using h
  have hprev := st86_p93
  have hstep := st86_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p95 : ((504049853921/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT86 (i+1))
      = (∑ i ∈ Finset.range 94, stT86 (i+1)) + stT86 95 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 94
    simpa using h
  have hprev := st86_p94
  have hstep := st86_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p96 : ((9577664564197/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT86 (i+1))
      = (∑ i ∈ Finset.range 95, stT86 (i+1)) + stT86 96 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 95
    simpa using h
  have hprev := st86_p95
  have hstep := st86_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p97 : ((2299439821159/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT86 (i+1))
      = (∑ i ∈ Finset.range 96, stT86 (i+1)) + stT86 97 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 96
    simpa using h
  have hprev := st86_p96
  have hstep := st86_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p98 : ((2304053942957/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT86 (i+1))
      = (∑ i ∈ Finset.range 97, stT86 (i+1)) + stT86 98 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 97
    simpa using h
  have hprev := st86_p97
  have hstep := st86_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p99 : ((120160494417/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT86 (i+1))
      = (∑ i ∈ Finset.range 98, stT86 (i+1)) + stT86 99 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 98
    simpa using h
  have hprev := st86_p98
  have hstep := st86_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st86_p100 : ((2525630765919/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT86 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT86 (i+1))
      = (∑ i ∈ Finset.range 99, stT86 (i+1)) + stT86 100 := by
    have h := Finset.sum_range_succ (fun i => stT86 (i+1)) 99
    simpa using h
  have hprev := st86_p99
  have hstep := st86_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 86`.** -/
theorem station_86_sign : 0 < hardyG (((86:ℕ)):ℝ) := by
  have hcore := phase_station_lower 86 100 (by norm_num) (by norm_num)
    ((29/40000 : ℚ) : ℝ)
  have hchain := st86_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT86 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((86:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((29/40000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((86:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((86:ℕ)):ℝ)+1) * ((((86:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((3499551/4300000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((2525630765919/1250000000000 : ℚ) : ℝ) - ((3499551/4300000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((29/40000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((86:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((29/40000 : ℚ) : ℝ)
        * (riemannZeta (line (((86:ℕ)):ℝ))).re
      - Real.sin ((29/40000 : ℚ) : ℝ)
        * (riemannZeta (line (((86:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((86:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((86:ℕ)):ℝ)
      = ((((86:ℕ)):ℝ) * (Real.log (((86:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((86:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_86
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
  have hθwin : |(((29/40000 : ℚ) : ℝ) + ((11:ℤ)) * (2*Real.pi)) - theta (((86:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((86:ℕ)):ℝ))
    (φ := ((29/40000 : ℚ) : ℝ) + ((11:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((29/40000 : ℚ)) : ℝ) 11).1,
    (cos_sin_shift (((29/40000 : ℚ)) : ℝ) 11).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_86_sign
end AxiomAudit
