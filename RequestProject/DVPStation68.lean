import RequestProject.DVPSqrtTable

/-!
# Station `t = 68` of the extended Hardy ladder (rung-74)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT68 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((68 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))

theorem st68_c1 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((214319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 676051/5000000) (δ := 21/100000000) (ψ := -540841/1000000) 68 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t1 : ((428613/500000 : ℚ) : ℝ) ≤ stT68 1 := by
  have hc : ((428613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((428613/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((428613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c2 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-852023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6476583/10000000) (δ := 547/100000000) (ψ := -540841/1000000) 68 8
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t2 : ((-1506266530991/2500000000000 : ℚ) : ℝ) ≤ stT68 2 := by
  have hc : ((-852073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1506266530991/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-852073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c3 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((247127/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47421/1250000) (δ := 59/10000000) (ψ := -540841/1000000) 68 12
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t3 : ((1426716059979/2500000000000 : ℚ) : ℝ) ≤ stT68 3 := by
  have hc : ((494229/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1426716059979/2500000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((494229/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c4 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((423341/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 701347/5000000) (δ := 191/50000000) (ψ := -540841/1000000) 68 15
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t4 : ((105829/250000 : ℚ) : ℝ) ≤ stT68 4 := by
  have hc : ((105829/125000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105829/250000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((105829/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c5 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-999639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -973349/1250000) (δ := 629/100000000) (ψ := -540841/1000000) 68 18
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t5 : ((-558843145713/1250000000000 : ℚ) : ℝ) ≤ stT68 5 := by
  have hc : ((-999689/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-558843145713/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-999689/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c6 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-989987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 749991/1000000) (δ := 93/20000000) (ψ := -540841/1000000) 68 19
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t6 : ((-4041809221871/10000000000000 : ℚ) : ℝ) ≤ stT68 6 := by
  have hc : ((-990037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4041809221871/10000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-990037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c7 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((4873/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2289599/10000000) (δ := 89/25000000) (ψ := -540841/1000000) 68 21
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t7 : ((23020866693/100000000000 : ℚ) : ℝ) ≤ stT68 7 := by
  have hc : ((24363/40000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23020866693/100000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((24363/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c8 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-168251/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6425991/10000000) (δ := 83/20000000) (ψ := -540841/1000000) 68 23
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t8 : ((-297446243187/1000000000000 : ℚ) : ℝ) ≤ stT68 8 := by
  have hc : ((-168261/200000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297446243187/1000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-168261/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c9 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((166057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1055419/5000000) (δ := 519/100000000) (ψ := -540841/1000000) 68 24
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t9 : ((1106963222637/5000000000000 : ℚ) : ℝ) ≤ stT68 9 := by
  have hc : ((332089/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1106963222637/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((332089/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c10 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((249829/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 46243/5000000) (δ := 609/100000000) (ψ := -540841/1000000) 68 25
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t10 : ((1579977944341/5000000000000 : ℚ) : ℝ) ≤ stT68 10 := by
  have hc : ((499633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1579977944341/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((499633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c11 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((972537/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 587253/10000000) (δ := 23/5000000) (ψ := -540841/1000000) 68 26
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t11 : ((2932158196031/10000000000000 : ℚ) : ℝ) ≤ stT68 11 := by
  have hc : ((972487/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2932158196031/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((972487/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c12 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((198273/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41097/1250000) (δ := 93/25000000) (ψ := -540841/1000000) 68 27
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t12 : ((572335913513/2000000000000 : ℚ) : ℝ) ≤ stT68 12 := by
  have hc : ((198263/200000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((572335913513/2000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((198263/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c13 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((563821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2429479/10000000) (δ := 181/50000000) (ψ := -540841/1000000) 68 28
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t13 : ((3127237737/20000000000 : ℚ) : ℝ) ≤ stT68 13 := by
  have hc : ((563771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3127237737/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((563771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c14 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-601069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5539087/10000000) (δ := 511/100000000) (ψ := -540841/1000000) 68 29
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t14 : ((-1606558453947/10000000000000 : ℚ) : ℝ) ≤ stT68 14 := by
  have hc : ((-601119/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1606558453947/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-601119/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c15 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-786477/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6189701/10000000) (δ := 711/100000000) (ψ := -540841/1000000) 68 29
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t15 : ((-2030804062203/10000000000000 : ℚ) : ℝ) ≤ stT68 15 := by
  have hc : ((-786527/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2030804062203/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-786527/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c16 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((835741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1453287/10000000) (δ := 27/5000000) (ψ := -540841/1000000) 68 30
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t16 : ((835691/4000000 : ℚ) : ℝ) ≤ stT68 16 := by
  have hc : ((835691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((835691/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((835691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c17 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-43/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3948491/10000000) (δ := 409/100000000) (ψ := -540841/1000000) 68 31
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t17 : ((-419586761/200000000000 : ℚ) : ℝ) ≤ stT68 17 := by
  have hc : ((-173/20000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-419586761/200000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-173/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c18 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-335879/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144211/250000) (δ := 197/50000000) (ψ := -540841/1000000) 68 31
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t18 : ((-24741670431/156250000000 : ℚ) : ℝ) ≤ stT68 18 := by
  have hc : ((-10497/15625 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24741670431/156250000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-10497/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c19 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((955561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11689/156250) (δ := 131/25000000) (ψ := -540841/1000000) 68 32
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t19 : ((2192092249227/10000000000000 : ℚ) : ℝ) ≤ stT68 19 := by
  have hc : ((955511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2192092249227/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((955511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c20 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-99889/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7736199/10000000) (δ := 99/20000000) (ψ := -540841/1000000) 68 33
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t20 : ((-27921222099/125000000000 : ℚ) : ℝ) ≤ stT68 20 := by
  have hc : ((-49947/50000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27921222099/125000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-49947/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c21 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((975183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 558129/10000000) (δ := 107/25000000) (ψ := -540841/1000000) 68 33
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t21 : ((1063956889837/5000000000000 : ℚ) : ℝ) ≤ stT68 21 := by
  have hc : ((975133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1063956889837/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((975133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c22 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-970133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -905179/1250000) (δ := 173/50000000) (ψ := -540841/1000000) 68 34
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t22 : ((-258554739683/1250000000000 : ℚ) : ℝ) ≤ stT68 22 := by
  have hc : ((-970183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-258554739683/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-970183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c23 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((496027/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39421/1250000) (δ := 577/100000000) (ψ := -540841/1000000) 68 34
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t23 : ((64639724643/312500000000 : ℚ) : ℝ) ≤ stT68 23 := by
  have hc : ((248001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64639724643/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((248001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c24 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-992641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3775251/5000000) (δ := 497/100000000) (ψ := -540841/1000000) 68 34
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t24 : ((-1013161281111/5000000000000 : ℚ) : ℝ) ≤ stT68 24 := by
  have hc : ((-992691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1013161281111/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-992691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c25 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((883699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -608861/5000000) (δ := 263/50000000) (ψ := -540841/1000000) 68 35
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t25 : ((883649/5000000 : ℚ) : ℝ) ≤ stT68 25 := by
  have hc : ((883649/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((883649/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((883649/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c26 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-572149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5449799/10000000) (δ := 223/50000000) (ψ := -540841/1000000) 68 35
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t26 : ((-561087467619/5000000000000 : ℚ) : ℝ) ≤ stT68 26 := by
  have hc : ((-572199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-561087467619/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-572199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c27 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((33867/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -960577/2500000) (δ := 447/100000000) (ψ := -540841/1000000) 68 36
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t27 : ((130161633/20000000000 : ℚ) : ℝ) ≤ stT68 27 := by
  have hc : ((33817/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((130161633/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((33817/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c28 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((74119/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2340191/10000000) (δ := 159/25000000) (ψ := -540841/1000000) 68 36
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t28 : ((280119810861/2500000000000 : ℚ) : ℝ) ≤ stT68 28 := by
  have hc : ((296451/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((280119810861/2500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((296451/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c29 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-983719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -925281/1250000) (δ := 101/20000000) (ψ := -540841/1000000) 68 37
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t29 : ((-913406889813/5000000000000 : ℚ) : ℝ) ≤ stT68 29 := by
  have hc : ((-983769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-913406889813/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-983769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c30 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((396343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204873/1250000) (δ := 269/50000000) (ψ := -540841/1000000) 68 37
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t30 : ((361787010819/2500000000000 : ℚ) : ℝ) ≤ stT68 30 := by
  have hc : ((198159/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((361787010819/2500000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((198159/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c31 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-1659/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1967643/5000000) (δ := 133/20000000) (ψ := -540841/1000000) 68 37
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t31 : ((-378069367/625000000000 : ℚ) : ℝ) ≤ stT68 31 := by
  have hc : ((-421/125000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378069367/625000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-421/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c32 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-830143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6375399/10000000) (δ := 347/50000000) (ψ := -540841/1000000) 68 38
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t32 : ((-1467587789031/10000000000000 : ℚ) : ℝ) ≤ stT68 32 := by
  have hc : ((-830193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1467587789031/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-830193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c33 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((897077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1144217/10000000) (δ := 389/100000000) (ψ := -540841/1000000) 68 38
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t33 : ((195190384119/1250000000000 : ℚ) : ℝ) ≤ stT68 33 := by
  have hc : ((897027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((195190384119/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((897027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c34 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-759/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3930787/10000000) (δ := 267/50000000) (ψ := -540841/1000000) 68 38
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t34 : ((-42017157/156250000000 : ℚ) : ℝ) ≤ stT68 34 := by
  have hc : ((-49/31250 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42017157/156250000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-49/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c35 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-920329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1369859/2000000) (δ := 1/250000) (ψ := -540841/1000000) 68 39
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t35 : ((-1555724907111/10000000000000 : ℚ) : ℝ) ≤ stT68 35 := by
  have hc : ((-920379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1555724907111/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-920379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c36 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((679219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1030123/5000000) (δ := 443/100000000) (ψ := -540841/1000000) 68 39
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t36 : ((565973940277/5000000000000 : ℚ) : ℝ) ≤ stT68 36 := by
  have hc : ((679169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((565973940277/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((679169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c37 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((101411/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 129879/500000) (δ := 603/100000000) (ψ := -540841/1000000) 68 39
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t37 : ((166702128589/2000000000000 : ℚ) : ℝ) ≤ stT68 37 := by
  have hc : ((101401/200000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((166702128589/2000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((101401/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c38 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-191699/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3565591/5000000) (δ := 1/250000) (ψ := -540841/1000000) 68 39
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t38 : ((-62198643087/400000000000 : ℚ) : ℝ) ≤ stT68 38 := by
  have hc : ((-191709/200000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62198643087/400000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-191709/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c39 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-93447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4160949/10000000) (δ := 393/100000000) (ψ := -540841/1000000) 68 40
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t39 : ((-74857531577/5000000000000 : ℚ) : ℝ) ≤ stT68 39 := by
  have hc : ((-93497/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-74857531577/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-93497/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c40 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((998363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 71539/5000000) (δ := 353/100000000) (ψ := -540841/1000000) 68 40
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t40 : ((789235310097/5000000000000 : ℚ) : ℝ) ≤ stT68 40 := by
  have hc : ((998313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((789235310097/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((998313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c41 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-82389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4340823/10000000) (δ := 9/2000000) (ψ := -540841/1000000) 68 40
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t41 : ((-32177268883/1250000000000 : ℚ) : ℝ) ≤ stT68 41 := by
  have hc : ((-41207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32177268883/1250000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-41207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c42 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-972893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7270557/10000000) (δ := 291/50000000) (ψ := -540841/1000000) 68 41
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t42 : ((-750642064531/5000000000000 : ℚ) : ℝ) ≤ stT68 42 := by
  have hc : ((-972943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750642064531/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-972943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c43 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((129819/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -817593/2500000) (δ := 291/50000000) (ψ := -540841/1000000) 68 41
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t43 : ((19793390309/500000000000 : ℚ) : ℝ) ≤ stT68 43 := by
  have hc : ((64897/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19793390309/500000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((64897/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c44 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((241907/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 318923/5000000) (δ := 231/50000000) (ψ := -540841/1000000) 68 41
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t44 : ((182334752421/1250000000000 : ℚ) : ℝ) ≤ stT68 44 := by
  have hc : ((483789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182334752421/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((483789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c45 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-2109/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4458231/10000000) (δ := 581/100000000) (ψ := -540841/1000000) 68 41
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t45 : ((-786164241/25000000000 : ℚ) : ℝ) ≤ stT68 45 := by
  have hc : ((-4219/20000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-786164241/25000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-4219/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c46 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-99073/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3756659/5000000) (δ := 79/12500000) (ψ := -540841/1000000) 68 42
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t46 : ((-3652064619/25000000000 : ℚ) : ℝ) ≤ stT68 46 := by
  have hc : ((-49539/50000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3652064619/25000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-49539/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c47 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((1743/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3857263/10000000) (δ := 691/100000000) (ψ := -540841/1000000) 68 42
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t47 : ((20302935431/5000000000000 : ℚ) : ℝ) ≤ stT68 47 := by
  have hc : ((13919/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20302935431/5000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((13919/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c48 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((124227/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -278183/10000000) (δ := 611/100000000) (ψ := -540841/1000000) 68 42
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t48 : ((5737508001/40000000000 : ℚ) : ℝ) ≤ stT68 48 := by
  have hc : ((496883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5737508001/40000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((496883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c49 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((69079/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645419/2000000) (δ := 79/12500000) (ψ := -540841/1000000) 68 42
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t49 : ((197332797943/5000000000000 : ℚ) : ℝ) ≤ stT68 49 := by
  have hc : ((138133/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((197332797943/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((138133/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c50 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-88839/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1665389/2500000) (δ := 651/100000000) (ψ := -540841/1000000) 68 42
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t50 : ((-15705553577/125000000000 : ℚ) : ℝ) ≤ stT68 50 := by
  have hc : ((-22211/25000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15705553577/125000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-22211/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c51 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-322563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5679961/10000000) (δ := 481/100000000) (ψ := -540841/1000000) 68 43
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t51 : ((-112928461807/1250000000000 : ℚ) : ℝ) ≤ stT68 51 := by
  have hc : ((-80647/125000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112928461807/1250000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-80647/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c52 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((290209/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1189443/5000000) (δ := 561/100000000) (ψ := -540841/1000000) 68 43
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t52 : ((201206331/2500000000 : ℚ) : ℝ) ≤ stT68 52 := by
  have hc : ((36273/62500 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201206331/2500000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((36273/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c53 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((941507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 859307/10000000) (δ := 601/100000000) (ψ := -540841/1000000) 68 43
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t53 : ((258638008497/2000000000000 : ℚ) : ℝ) ≤ stT68 53 := by
  have hc : ((941457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258638008497/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((941457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c54 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-43977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4036969/10000000) (δ := 401/100000000) (ψ := -540841/1000000) 68 43
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t54 : ((-14978293589/2500000000000 : ℚ) : ℝ) ≤ stT68 54 := by
  have hc : ((-44027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14978293589/2500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-44027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c55 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-480657/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7156323/10000000) (δ := 281/50000000) (ψ := -540841/1000000) 68 43
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t55 : ((-810189511/6250000000 : ℚ) : ℝ) ≤ stT68 55 := by
  have hc : ((-240341/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-810189511/6250000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-240341/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c56 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-292387/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2744247/5000000) (δ := 613/100000000) (ψ := -540841/1000000) 68 44
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t56 : ((-97688050621/1250000000000 : ℚ) : ℝ) ≤ stT68 56 := by
  have hc : ((-73103/125000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97688050621/1250000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-73103/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c57 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((273581/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1239783/5000000) (δ := 453/100000000) (ψ := -540841/1000000) 68 44
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t57 : ((22645854737/312500000000 : ℚ) : ℝ) ≤ stT68 57 := by
  have hc : ((68389/125000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22645854737/312500000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((68389/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c58 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((981851/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 47703/1000000) (δ := 63/10000000) (ψ := -540841/1000000) 68 44
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t58 : ((161145943533/1250000000000 : ℚ) : ℝ) ≤ stT68 58 := by
  have hc : ((981801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161145943533/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((981801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c59 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((4317/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 845771/2500000) (δ := 39/10000000) (ψ := -540841/1000000) 68 44
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t59 : ((1404738231/50000000000 : ℚ) : ℝ) ≤ stT68 59 := by
  have hc : ((1079/5000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1404738231/50000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((1079/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c60 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-399407/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3120147/5000000) (δ := 413/100000000) (ψ := -540841/1000000) 68 44
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t60 : ((-12891617871/125000000000 : ℚ) : ℝ) ≤ stT68 60 := by
  have hc : ((-49929/62500 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12891617871/125000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-49929/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c61 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-887679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -832211/1250000) (δ := 53/12500000) (ψ := -540841/1000000) 68 45
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t61 : ((-1136620692001/10000000000000 : ℚ) : ℝ) ≤ stT68 61 := by
  have hc : ((-887729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1136620692001/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-887729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c62 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((3359/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -19467/50000) (δ := 17/3125000) (ψ := -540841/1000000) 68 45
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t62 : ((8500116693/5000000000000 : ℚ) : ℝ) ≤ stT68 62 := by
  have hc : ((6693/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8500116693/5000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((6693/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c63 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((222967/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -586671/5000000) (δ := 539/100000000) (ψ := -540841/1000000) 68 45
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t63 : ((561792276829/5000000000000 : ℚ) : ℝ) ≤ stT68 63 := by
  have hc : ((445909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((561792276829/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((445909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c64 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((824459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1503879/10000000) (δ := 17/3125000) (ψ := -540841/1000000) 68 45
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t64 : ((824409/8000000 : ℚ) : ℝ) ≤ stT68 64 := by
  have hc : ((824409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((824409/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((824409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c65 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-42469/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4139591/10000000) (δ := 29/6250000) (ψ := -540841/1000000) 68 45
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t65 : ((-6588418489/625000000000 : ℚ) : ℝ) ≤ stT68 65 := by
  have hc : ((-21247/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6588418489/625000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-21247/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c66 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-450751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6735061/10000000) (δ := 419/100000000) (ψ := -540841/1000000) 68 45
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t66 : ((-13871673501/125000000000 : ℚ) : ℝ) ≤ stT68 66 := by
  have hc : ((-56347/62500 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13871673501/125000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-56347/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c67 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-209797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6416463/10000000) (δ := 71/12500000) (ψ := -540841/1000000) 68 46
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t67 : ((-102529286841/1000000000000 : ℚ) : ℝ) ≤ stT68 67 := by
  have hc : ((-419619/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102529286841/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-419619/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c68 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((11637/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1948949/5000000) (δ := 81/12500000) (ψ := -540841/1000000) 68 46
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t68 : ((7025649993/5000000000000 : ℚ) : ℝ) ≤ stT68 68 := by
  have hc : ((11587/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7025649993/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((11587/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c69 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((105477/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1416103/10000000) (δ := 43/6250000) (ψ := -540841/1000000) 68 46
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t69 : ((253943612307/2500000000000 : ℚ) : ℝ) ≤ stT68 69 := by
  have hc : ((421883/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253943612307/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((421883/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c70 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((229081/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1029983/10000000) (δ := 51/12500000) (ψ := -540841/1000000) 68 46
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t70 : ((136894542559/1250000000000 : ℚ) : ℝ) ≤ stT68 70 := by
  have hc : ((458137/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136894542559/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((458137/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c71 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((193029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3441371/10000000) (δ := 103/20000000) (ψ := -540841/1000000) 68 46
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t71 : ((229023810599/10000000000000 : ℚ) : ℝ) ≤ stT68 71 := by
  have hc : ((192979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((229023810599/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((192979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c72 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-68661/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 727379/1250000) (δ := 71/12500000) (ψ := -540841/1000000) 68 46
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t72 : ((-2528865781/31250000000 : ℚ) : ℝ) ≤ stT68 72 := by
  have hc : ((-34333/50000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2528865781/31250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-34333/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c73 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-496163/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7544067/10000000) (δ := 219/50000000) (ψ := -540841/1000000) 68 47
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t73 : ((-36296524341/312500000000 : ℚ) : ℝ) ≤ stT68 73 := by
  have hc : ((-124047/125000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36296524341/312500000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-124047/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c74 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-124577/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2615553/5000000) (δ := 121/20000000) (ψ := -540841/1000000) 68 47
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t74 : ((-289664856383/5000000000000 : ℚ) : ℝ) ≤ stT68 74 := by
  have hc : ((-249179/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289664856383/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-249179/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c75 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((47653/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -368649/1250000) (δ := 299/50000000) (ψ := -540841/1000000) 68 47
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t75 : ((2200708089/50000000000 : ℚ) : ℝ) ≤ stT68 75 := by
  have hc : ((190587/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2200708089/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((190587/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c76 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((961331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -21797/312500) (δ := 219/50000000) (ψ := -540841/1000000) 68 47
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t76 : ((551332143459/5000000000000 : ℚ) : ℝ) ≤ stT68 76 := by
  have hc : ((961281/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((551332143459/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((961281/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c77 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((163941/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6099/40000) (δ := 279/50000000) (ψ := -540841/1000000) 68 47
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t77 : ((37363317451/400000000000 : ℚ) : ℝ) ≤ stT68 77 := by
  have hc : ((163931/200000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37363317451/400000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((163931/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c78 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((10421/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3718329/10000000) (δ := 259/50000000) (ψ := -540841/1000000) 68 47
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t78 : ((47169527543/5000000000000 : ℚ) : ℝ) ≤ stT68 78 := by
  have hc : ((41659/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47169527543/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((41659/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c79 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-705259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5883963/10000000) (δ := 179/50000000) (ψ := -540841/1000000) 68 47
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t79 : ((-24797959131/312500000000 : ℚ) : ℝ) ≤ stT68 79 := by
  have hc : ((-705309/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24797959131/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-705309/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c80 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-997733/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7685607/10000000) (δ := 467/100000000) (ψ := -540841/1000000) 68 48
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t80 : ((-557777659311/5000000000000 : ℚ) : ℝ) ≤ stT68 80 := by
  have hc : ((-997783/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-557777659311/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-997783/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c81 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-612101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5573779/10000000) (δ := 347/100000000) (ψ := -540841/1000000) 68 48
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t81 : ((-85021040239/1250000000000 : ℚ) : ℝ) ≤ stT68 81 := by
  have hc : ((-612151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85021040239/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-612151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c82 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((174749/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3487863/10000000) (δ := 387/100000000) (ψ := -540841/1000000) 68 48
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t82 : ((38584545237/2000000000000 : ℚ) : ℝ) ≤ stT68 82 := by
  have hc : ((174699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38584545237/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((174699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c83 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((841419/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -44601/312500) (δ := 667/100000000) (ψ := -540841/1000000) 68 48
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t83 : ((461760975949/5000000000000 : ℚ) : ℝ) ≤ stT68 83 := by
  have hc : ((841369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((461760975949/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((841369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c84 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((970503/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 608721/10000000) (δ := 707/100000000) (ψ := -540841/1000000) 68 48
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t84 : ((1058850593317/10000000000000 : ℚ) : ℝ) ≤ stT68 84 := by
  have hc : ((970453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1058850593317/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((970453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c85 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((15597/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2620579/10000000) (δ := 47/12500000) (ψ := -540841/1000000) 68 48
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t85 : ((67662489901/1250000000000 : ℚ) : ℝ) ≤ stT68 85 := by
  have hc : ((249527/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67662489901/1250000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((249527/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c86 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-67349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2304453/5000000) (δ := 41/6250000) (ψ := -540841/1000000) 68 48
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t86 : ((-18159447893/625000000000 : ℚ) : ℝ) ≤ stT68 86 := by
  have hc : ((-134723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18159447893/625000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-134723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c87 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-435909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1314849/2000000) (δ := 587/100000000) (ψ := -540841/1000000) 68 48
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t87 : ((-233685254271/2500000000000 : ℚ) : ℝ) ≤ stT68 87 := by
  have hc : ((-217967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233685254271/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-217967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c88 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-38601/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179771/250000) (δ := 77/12500000) (ψ := -540841/1000000) 68 49
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t88 : ((-10287738103/100000000000 : ℚ) : ℝ) ≤ stT68 88 := by
  have hc : ((-38603/40000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10287738103/100000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-38603/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c89 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-255853/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1053983/2000000) (δ := 467/100000000) (ψ := -540841/1000000) 68 49
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t89 : ((-67807542061/1250000000000 : ℚ) : ℝ) ≤ stT68 89 := by
  have hc : ((-127939/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67807542061/1250000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-127939/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c90 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((220781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1685227/5000000) (δ := 467/100000000) (ψ := -540841/1000000) 68 49
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t90 : ((58167695313/2500000000000 : ℚ) : ℝ) ≤ stT68 90 := by
  have hc : ((220731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58167695313/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((220731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c91 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((413571/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -745991/5000000) (δ := 707/100000000) (ψ := -540841/1000000) 68 49
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t91 : ((54189206883/625000000000 : ℚ) : ℝ) ≤ stT68 91 := by
  have hc : ((206773/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54189206883/625000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((206773/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c92 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((197861/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 9149/250000) (δ := 507/100000000) (ψ := -540841/1000000) 68 49
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t92 : ((51568478193/500000000000 : ℚ) : ℝ) ≤ stT68 92 := by
  have hc : ((197851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51568478193/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((197851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c93 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((317987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 275477/1250000) (δ := 627/100000000) (ψ := -540841/1000000) 68 49
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t93 : ((164855506931/2500000000000 : ℚ) : ℝ) ≤ stT68 93 := by
  have hc : ((158981/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164855506931/2500000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((158981/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c94 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-38001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 804403/2000000) (δ := 547/100000000) (ψ := -540841/1000000) 68 49
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t94 : ((-19623319261/5000000000000 : ℚ) : ℝ) ≤ stT68 94 := by
  have hc : ((-38051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19623319261/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-38051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c95 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-27487/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5820973/10000000) (δ := 587/100000000) (ψ := -540841/1000000) 68 49
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t95 : ((-28203136731/400000000000 : ℚ) : ℝ) ≤ stT68 95 := by
  have hc : ((-27489/40000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28203136731/400000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-27489/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c96 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-124361/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3800547/5000000) (δ := 587/100000000) (ψ := -540841/1000000) 68 49
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t96 : ((-507727308249/5000000000000 : ℚ) : ℝ) ≤ stT68 96 := by
  have hc : ((-497469/500000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-507727308249/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-497469/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c97 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-411673/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1269039/2000000) (δ := 517/100000000) (ψ := -540841/1000000) 68 50
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t97 : ((-209008164603/2500000000000 : ℚ) : ℝ) ≤ stT68 97 := by
  have hc : ((-205849/250000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-209008164603/2500000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-205849/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c98 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((-266577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -460159/1000000) (δ := 517/100000000) (ψ := -540841/1000000) 68 50
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t98 : ((-269334063931/10000000000000 : ℚ) : ℝ) ≤ stT68 98 := by
  have hc : ((-266627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-269334063931/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-266627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c99 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((408237/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2875687/10000000) (δ := 183/50000000) (ψ := -540841/1000000) 68 50
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t99 : ((410243037919/10000000000000 : ℚ) : ℝ) ≤ stT68 99 := by
  have hc : ((408187/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((410243037919/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((408187/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_c100 :
    |Real.cos (((68 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ))
      - ((89299/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116713/1000000) (δ := 557/100000000) (ψ := -540841/1000000) 68 50
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st68_t100 : ((44646955353/500000000000 : ℚ) : ℝ) ≤ stT68 100 := by
  have hc : ((44647/50000 : ℚ) : ℝ)
      ≤ Real.cos (((68 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-540841/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st68_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44646955353/500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((44647/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st68_p1 : ((428613/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT68 (i+1) := by
  rw [Finset.sum_range_one]
  exact st68_t1

theorem st68_p2 : ((636798469009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT68 (i+1))
      = (∑ i ∈ Finset.range 1, stT68 (i+1)) + stT68 2 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 1
    simpa using h
  have hprev := st68_p1
  have hstep := st68_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p3 : ((515878632247/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT68 (i+1))
      = (∑ i ∈ Finset.range 2, stT68 (i+1)) + stT68 3 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 2
    simpa using h
  have hprev := st68_p2
  have hstep := st68_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p4 : ((780451132247/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT68 (i+1))
      = (∑ i ∈ Finset.range 3, stT68 (i+1)) + stT68 4 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 3
    simpa using h
  have hprev := st68_p3
  have hstep := st68_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p5 : ((1002059118781/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT68 (i+1))
      = (∑ i ∈ Finset.range 4, stT68 (i+1)) + stT68 5 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 4
    simpa using h
  have hprev := st68_p4
  have hstep := st68_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p6 : ((3974663728377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT68 (i+1))
      = (∑ i ∈ Finset.range 5, stT68 (i+1)) + stT68 6 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 5
    simpa using h
  have hprev := st68_p5
  have hstep := st68_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p7 : ((6276750397677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT68 (i+1))
      = (∑ i ∈ Finset.range 6, stT68 (i+1)) + stT68 7 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 6
    simpa using h
  have hprev := st68_p6
  have hstep := st68_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p8 : ((3302287965807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT68 (i+1))
      = (∑ i ∈ Finset.range 7, stT68 (i+1)) + stT68 8 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 7
    simpa using h
  have hprev := st68_p7
  have hstep := st68_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p9 : ((5516214411081/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT68 (i+1))
      = (∑ i ∈ Finset.range 8, stT68 (i+1)) + stT68 9 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 8
    simpa using h
  have hprev := st68_p8
  have hstep := st68_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p10 : ((8676170299763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT68 (i+1))
      = (∑ i ∈ Finset.range 9, stT68 (i+1)) + stT68 10 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 9
    simpa using h
  have hprev := st68_p9
  have hstep := st68_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p11 : ((5804164247897/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT68 (i+1))
      = (∑ i ∈ Finset.range 10, stT68 (i+1)) + stT68 11 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 10
    simpa using h
  have hprev := st68_p10
  have hstep := st68_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p12 : ((14470008063359/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT68 (i+1))
      = (∑ i ∈ Finset.range 11, stT68 (i+1)) + stT68 12 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 11
    simpa using h
  have hprev := st68_p11
  have hstep := st68_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p13 : ((16033626931859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT68 (i+1))
      = (∑ i ∈ Finset.range 12, stT68 (i+1)) + stT68 13 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 12
    simpa using h
  have hprev := st68_p12
  have hstep := st68_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p14 : ((1803383559739/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT68 (i+1))
      = (∑ i ∈ Finset.range 13, stT68 (i+1)) + stT68 14 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 13
    simpa using h
  have hprev := st68_p13
  have hstep := st68_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p15 : ((12396264415709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT68 (i+1))
      = (∑ i ∈ Finset.range 14, stT68 (i+1)) + stT68 15 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 14
    simpa using h
  have hprev := st68_p14
  have hstep := st68_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p16 : ((14485491915709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT68 (i+1))
      = (∑ i ∈ Finset.range 15, stT68 (i+1)) + stT68 16 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 15
    simpa using h
  have hprev := st68_p15
  have hstep := st68_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p17 : ((14464512577659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT68 (i+1))
      = (∑ i ∈ Finset.range 16, stT68 (i+1)) + stT68 17 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 16
    simpa using h
  have hprev := st68_p16
  have hstep := st68_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p18 : ((515241826803/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT68 (i+1))
      = (∑ i ∈ Finset.range 17, stT68 (i+1)) + stT68 18 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 17
    simpa using h
  have hprev := st68_p17
  have hstep := st68_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p19 : ((7536568959651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT68 (i+1))
      = (∑ i ∈ Finset.range 18, stT68 (i+1)) + stT68 19 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 18
    simpa using h
  have hprev := st68_p18
  have hstep := st68_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p20 : ((6419720075691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT68 (i+1))
      = (∑ i ∈ Finset.range 19, stT68 (i+1)) + stT68 20 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 19
    simpa using h
  have hprev := st68_p19
  have hstep := st68_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p21 : ((935459620691/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT68 (i+1))
      = (∑ i ∈ Finset.range 20, stT68 (i+1)) + stT68 21 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 20
    simpa using h
  have hprev := st68_p20
  have hstep := st68_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p22 : ((1612364501699/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT68 (i+1))
      = (∑ i ∈ Finset.range 21, stT68 (i+1)) + stT68 22 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 21
    simpa using h
  have hprev := st68_p21
  have hstep := st68_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p23 : ((1870923400271/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT68 (i+1))
      = (∑ i ∈ Finset.range 22, stT68 (i+1)) + stT68 23 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 22
    simpa using h
  have hprev := st68_p22
  have hstep := st68_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p24 : ((6470532319973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT68 (i+1))
      = (∑ i ∈ Finset.range 23, stT68 (i+1)) + stT68 24 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 23
    simpa using h
  have hprev := st68_p23
  have hstep := st68_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p25 : ((7354181319973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT68 (i+1))
      = (∑ i ∈ Finset.range 24, stT68 (i+1)) + stT68 25 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 24
    simpa using h
  have hprev := st68_p24
  have hstep := st68_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p26 : ((3396546926177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT68 (i+1))
      = (∑ i ∈ Finset.range 25, stT68 (i+1)) + stT68 26 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 25
    simpa using h
  have hprev := st68_p25
  have hstep := st68_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p27 : ((1706408565151/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT68 (i+1))
      = (∑ i ∈ Finset.range 26, stT68 (i+1)) + stT68 27 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 26
    simpa using h
  have hprev := st68_p26
  have hstep := st68_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p28 : ((3692936941163/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT68 (i+1))
      = (∑ i ∈ Finset.range 27, stT68 (i+1)) + stT68 28 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 27
    simpa using h
  have hprev := st68_p27
  have hstep := st68_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p29 : ((6472466992513/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT68 (i+1))
      = (∑ i ∈ Finset.range 28, stT68 (i+1)) + stT68 29 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 28
    simpa using h
  have hprev := st68_p28
  have hstep := st68_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p30 : ((7196041014151/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT68 (i+1))
      = (∑ i ∈ Finset.range 29, stT68 (i+1)) + stT68 30 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 29
    simpa using h
  have hprev := st68_p29
  have hstep := st68_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p31 : ((1438603291843/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT68 (i+1))
      = (∑ i ∈ Finset.range 30, stT68 (i+1)) + stT68 31 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 30
    simpa using h
  have hprev := st68_p30
  have hstep := st68_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p32 : ((12918445129399/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT68 (i+1))
      = (∑ i ∈ Finset.range 31, stT68 (i+1)) + stT68 32 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 31
    simpa using h
  have hprev := st68_p31
  have hstep := st68_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p33 : ((14479968202351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT68 (i+1))
      = (∑ i ∈ Finset.range 32, stT68 (i+1)) + stT68 33 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 32
    simpa using h
  have hprev := st68_p32
  have hstep := st68_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p34 : ((14477279104303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT68 (i+1))
      = (∑ i ∈ Finset.range 33, stT68 (i+1)) + stT68 34 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 33
    simpa using h
  have hprev := st68_p33
  have hstep := st68_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p35 : ((1615194274649/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT68 (i+1))
      = (∑ i ∈ Finset.range 34, stT68 (i+1)) + stT68 35 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 34
    simpa using h
  have hprev := st68_p34
  have hstep := st68_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p36 : ((7026751038873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT68 (i+1))
      = (∑ i ∈ Finset.range 35, stT68 (i+1)) + stT68 36 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 35
    simpa using h
  have hprev := st68_p35
  have hstep := st68_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p37 : ((14887012720691/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT68 (i+1))
      = (∑ i ∈ Finset.range 36, stT68 (i+1)) + stT68 37 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 36
    simpa using h
  have hprev := st68_p36
  have hstep := st68_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p38 : ((3333011660879/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT68 (i+1))
      = (∑ i ∈ Finset.range 37, stT68 (i+1)) + stT68 38 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 37
    simpa using h
  have hprev := st68_p37
  have hstep := st68_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p39 : ((6591165790181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT68 (i+1))
      = (∑ i ∈ Finset.range 38, stT68 (i+1)) + stT68 39 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 38
    simpa using h
  have hprev := st68_p38
  have hstep := st68_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p40 : ((3690200550139/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT68 (i+1))
      = (∑ i ∈ Finset.range 39, stT68 (i+1)) + stT68 40 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 39
    simpa using h
  have hprev := st68_p39
  have hstep := st68_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p41 : ((3625846012373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT68 (i+1))
      = (∑ i ∈ Finset.range 40, stT68 (i+1)) + stT68 41 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 40
    simpa using h
  have hprev := st68_p40
  have hstep := st68_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p42 : ((1300209992043/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT68 (i+1))
      = (∑ i ∈ Finset.range 41, stT68 (i+1)) + stT68 42 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 41
    simpa using h
  have hprev := st68_p41
  have hstep := st68_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p43 : ((1339796772661/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT68 (i+1))
      = (∑ i ∈ Finset.range 42, stT68 (i+1)) + stT68 43 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 42
    simpa using h
  have hprev := st68_p42
  have hstep := st68_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p44 : ((7428322872989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT68 (i+1))
      = (∑ i ∈ Finset.range 43, stT68 (i+1)) + stT68 44 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 43
    simpa using h
  have hprev := st68_p43
  have hstep := st68_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p45 : ((7271090024789/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT68 (i+1))
      = (∑ i ∈ Finset.range 44, stT68 (i+1)) + stT68 45 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 44
    simpa using h
  have hprev := st68_p44
  have hstep := st68_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p46 : ((6540677100989/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT68 (i+1))
      = (∑ i ∈ Finset.range 45, stT68 (i+1)) + stT68 46 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 45
    simpa using h
  have hprev := st68_p45
  have hstep := st68_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p47 : ((328049001821/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT68 (i+1))
      = (∑ i ∈ Finset.range 46, stT68 (i+1)) + stT68 47 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 46
    simpa using h
  have hprev := st68_p46
  have hstep := st68_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p48 : ((1455633707309/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT68 (i+1))
      = (∑ i ∈ Finset.range 47, stT68 (i+1)) + stT68 48 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 47
    simpa using h
  have hprev := st68_p47
  have hstep := st68_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p49 : ((934437666811/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT68 (i+1))
      = (∑ i ∈ Finset.range 48, stT68 (i+1)) + stT68 49 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 48
    simpa using h
  have hprev := st68_p48
  have hstep := st68_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p50 : ((427954949463/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT68 (i+1))
      = (∑ i ∈ Finset.range 49, stT68 (i+1)) + stT68 50 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 49
    simpa using h
  have hprev := st68_p49
  have hstep := st68_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p51 : ((319778267209/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT68 (i+1))
      = (∑ i ∈ Finset.range 50, stT68 (i+1)) + stT68 51 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 50
    simpa using h
  have hprev := st68_p50
  have hstep := st68_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p52 : ((339898900309/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT68 (i+1))
      = (∑ i ∈ Finset.range 51, stT68 (i+1)) + stT68 52 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 51
    simpa using h
  have hprev := st68_p51
  have hstep := st68_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p53 : ((2977829210969/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT68 (i+1))
      = (∑ i ∈ Finset.range 52, stT68 (i+1)) + stT68 53 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 52
    simpa using h
  have hprev := st68_p52
  have hstep := st68_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p54 : ((14829232880489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT68 (i+1))
      = (∑ i ∈ Finset.range 53, stT68 (i+1)) + stT68 54 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 53
    simpa using h
  have hprev := st68_p53
  have hstep := st68_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p55 : ((13532929662889/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT68 (i+1))
      = (∑ i ∈ Finset.range 54, stT68 (i+1)) + stT68 55 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 54
    simpa using h
  have hprev := st68_p54
  have hstep := st68_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p56 : ((12751425257921/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT68 (i+1))
      = (∑ i ∈ Finset.range 55, stT68 (i+1)) + stT68 56 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 55
    simpa using h
  have hprev := st68_p55
  have hstep := st68_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p57 : ((2695218521901/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT68 (i+1))
      = (∑ i ∈ Finset.range 56, stT68 (i+1)) + stT68 57 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 56
    simpa using h
  have hprev := st68_p56
  have hstep := st68_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p58 : ((14765260157769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT68 (i+1))
      = (∑ i ∈ Finset.range 57, stT68 (i+1)) + stT68 58 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 57
    simpa using h
  have hprev := st68_p57
  have hstep := st68_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p59 : ((15046207803969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT68 (i+1))
      = (∑ i ∈ Finset.range 58, stT68 (i+1)) + stT68 59 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 58
    simpa using h
  have hprev := st68_p58
  have hstep := st68_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p60 : ((14014878374289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT68 (i+1))
      = (∑ i ∈ Finset.range 59, stT68 (i+1)) + stT68 60 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 59
    simpa using h
  have hprev := st68_p59
  have hstep := st68_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p61 : ((804891105143/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT68 (i+1))
      = (∑ i ∈ Finset.range 60, stT68 (i+1)) + stT68 61 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 60
    simpa using h
  have hprev := st68_p60
  have hstep := st68_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p62 : ((6447628957837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT68 (i+1))
      = (∑ i ∈ Finset.range 61, stT68 (i+1)) + stT68 62 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 61
    simpa using h
  have hprev := st68_p61
  have hstep := st68_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p63 : ((3504710617333/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT68 (i+1))
      = (∑ i ∈ Finset.range 62, stT68 (i+1)) + stT68 63 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 62
    simpa using h
  have hprev := st68_p62
  have hstep := st68_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p64 : ((3762338429833/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT68 (i+1))
      = (∑ i ∈ Finset.range 63, stT68 (i+1)) + stT68 64 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 63
    simpa using h
  have hprev := st68_p63
  have hstep := st68_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p65 : ((3735984755877/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT68 (i+1))
      = (∑ i ∈ Finset.range 64, stT68 (i+1)) + stT68 65 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 64
    simpa using h
  have hprev := st68_p64
  have hstep := st68_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p66 : ((3458551285857/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT68 (i+1))
      = (∑ i ∈ Finset.range 65, stT68 (i+1)) + stT68 66 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 65
    simpa using h
  have hprev := st68_p65
  have hstep := st68_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p67 : ((6404456137509/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT68 (i+1))
      = (∑ i ∈ Finset.range 66, stT68 (i+1)) + stT68 67 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 66
    simpa using h
  have hprev := st68_p66
  have hstep := st68_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p68 : ((3205740893751/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT68 (i+1))
      = (∑ i ∈ Finset.range 67, stT68 (i+1)) + stT68 68 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 67
    simpa using h
  have hprev := st68_p67
  have hstep := st68_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p69 : ((1729842253029/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT68 (i+1))
      = (∑ i ∈ Finset.range 68, stT68 (i+1)) + stT68 69 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 68
    simpa using h
  have hprev := st68_p68
  have hstep := st68_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p70 : ((466684198897/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT68 (i+1))
      = (∑ i ∈ Finset.range 69, stT68 (i+1)) + stT68 70 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 69
    simpa using h
  have hprev := st68_p69
  have hstep := st68_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p71 : ((15162918175303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT68 (i+1))
      = (∑ i ∈ Finset.range 70, stT68 (i+1)) + stT68 71 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 70
    simpa using h
  have hprev := st68_p70
  have hstep := st68_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p72 : ((14353681125383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT68 (i+1))
      = (∑ i ∈ Finset.range 71, stT68 (i+1)) + stT68 72 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 71
    simpa using h
  have hprev := st68_p71
  have hstep := st68_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p73 : ((13192192346471/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT68 (i+1))
      = (∑ i ∈ Finset.range 72, stT68 (i+1)) + stT68 73 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 72
    simpa using h
  have hprev := st68_p72
  have hstep := st68_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p74 : ((2522572526741/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT68 (i+1))
      = (∑ i ∈ Finset.range 73, stT68 (i+1)) + stT68 74 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 73
    simpa using h
  have hprev := st68_p73
  have hstep := st68_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p75 : ((2610600850301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT68 (i+1))
      = (∑ i ∈ Finset.range 74, stT68 (i+1)) + stT68 75 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 74
    simpa using h
  have hprev := st68_p74
  have hstep := st68_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p76 : ((14155668538423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT68 (i+1))
      = (∑ i ∈ Finset.range 75, stT68 (i+1)) + stT68 76 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 75
    simpa using h
  have hprev := st68_p75
  have hstep := st68_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p77 : ((7544875737349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT68 (i+1))
      = (∑ i ∈ Finset.range 76, stT68 (i+1)) + stT68 77 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 76
    simpa using h
  have hprev := st68_p76
  have hstep := st68_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p78 : ((1898011316223/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT68 (i+1))
      = (∑ i ∈ Finset.range 77, stT68 (i+1)) + stT68 78 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 77
    simpa using h
  have hprev := st68_p77
  have hstep := st68_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p79 : ((1798819479699/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT68 (i+1))
      = (∑ i ∈ Finset.range 78, stT68 (i+1)) + stT68 79 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 78
    simpa using h
  have hprev := st68_p78
  have hstep := st68_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p80 : ((1327500051897/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT68 (i+1))
      = (∑ i ∈ Finset.range 79, stT68 (i+1)) + stT68 80 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 79
    simpa using h
  have hprev := st68_p79
  have hstep := st68_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p81 : ((6297416098529/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT68 (i+1))
      = (∑ i ∈ Finset.range 80, stT68 (i+1)) + stT68 81 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 80
    simpa using h
  have hprev := st68_p80
  have hstep := st68_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p82 : ((12787754923243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT68 (i+1))
      = (∑ i ∈ Finset.range 81, stT68 (i+1)) + stT68 82 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 81
    simpa using h
  have hprev := st68_p81
  have hstep := st68_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p83 : ((13711276875141/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT68 (i+1))
      = (∑ i ∈ Finset.range 82, stT68 (i+1)) + stT68 83 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 82
    simpa using h
  have hprev := st68_p82
  have hstep := st68_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p84 : ((7385063734229/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT68 (i+1))
      = (∑ i ∈ Finset.range 83, stT68 (i+1)) + stT68 84 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 83
    simpa using h
  have hprev := st68_p83
  have hstep := st68_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p85 : ((7655713693833/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT68 (i+1))
      = (∑ i ∈ Finset.range 84, stT68 (i+1)) + stT68 85 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 84
    simpa using h
  have hprev := st68_p84
  have hstep := st68_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p86 : ((7510438110689/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT68 (i+1))
      = (∑ i ∈ Finset.range 85, stT68 (i+1)) + stT68 86 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 85
    simpa using h
  have hprev := st68_p85
  have hstep := st68_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p87 : ((7043067602147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT68 (i+1))
      = (∑ i ∈ Finset.range 86, stT68 (i+1)) + stT68 87 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 86
    simpa using h
  have hprev := st68_p86
  have hstep := st68_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p88 : ((6528680696997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT68 (i+1))
      = (∑ i ∈ Finset.range 87, stT68 (i+1)) + stT68 88 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 87
    simpa using h
  have hprev := st68_p87
  have hstep := st68_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p89 : ((6257450528753/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT68 (i+1))
      = (∑ i ∈ Finset.range 88, stT68 (i+1)) + stT68 89 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 88
    simpa using h
  have hprev := st68_p88
  have hstep := st68_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p90 : ((6373785919379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT68 (i+1))
      = (∑ i ∈ Finset.range 89, stT68 (i+1)) + stT68 90 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 89
    simpa using h
  have hprev := st68_p89
  have hstep := st68_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p91 : ((6807299574443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT68 (i+1))
      = (∑ i ∈ Finset.range 90, stT68 (i+1)) + stT68 91 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 90
    simpa using h
  have hprev := st68_p90
  have hstep := st68_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p92 : ((7322984356373/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT68 (i+1))
      = (∑ i ∈ Finset.range 91, stT68 (i+1)) + stT68 92 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 91
    simpa using h
  have hprev := st68_p91
  have hstep := st68_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p93 : ((1530539074047/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT68 (i+1))
      = (∑ i ∈ Finset.range 92, stT68 (i+1)) + stT68 93 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 92
    simpa using h
  have hprev := st68_p92
  have hstep := st68_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p94 : ((3816536025487/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT68 (i+1))
      = (∑ i ∈ Finset.range 93, stT68 (i+1)) + stT68 94 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 93
    simpa using h
  have hprev := st68_p93
  have hstep := st68_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p95 : ((14561065683673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT68 (i+1))
      = (∑ i ∈ Finset.range 94, stT68 (i+1)) + stT68 95 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 94
    simpa using h
  have hprev := st68_p94
  have hstep := st68_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p96 : ((541824442687/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT68 (i+1))
      = (∑ i ∈ Finset.range 95, stT68 (i+1)) + stT68 96 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 95
    simpa using h
  have hprev := st68_p95
  have hstep := st68_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p97 : ((12709578408763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT68 (i+1))
      = (∑ i ∈ Finset.range 96, stT68 (i+1)) + stT68 97 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 96
    simpa using h
  have hprev := st68_p96
  have hstep := st68_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p98 : ((6074338059/4882812500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT68 (i+1))
      = (∑ i ∈ Finset.range 97, stT68 (i+1)) + stT68 98 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 97
    simpa using h
  have hprev := st68_p97
  have hstep := st68_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p99 : ((12850487382751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT68 (i+1))
      = (∑ i ∈ Finset.range 98, stT68 (i+1)) + stT68 99 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 98
    simpa using h
  have hprev := st68_p98
  have hstep := st68_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st68_p100 : ((13743426489811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT68 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT68 (i+1))
      = (∑ i ∈ Finset.range 99, stT68 (i+1)) + stT68 100 := by
    have h := Finset.sum_range_succ (fun i => stT68 (i+1)) 99
    simpa using h
  have hprev := st68_p99
  have hstep := st68_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 68`.** -/
theorem station_68_sign : hardyG (((68:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 68 100 (by norm_num) (by norm_num)
    ((-540841/1000000 : ℚ) : ℝ)
  have hchain := st68_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT68 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((68:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-540841/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((68:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((68:ℕ)):ℝ)+1) * ((((68:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((823611/1360000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((13743426489811/10000000000000 : ℚ) : ℝ) - ((823611/1360000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-540841/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((68:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-540841/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((68:ℕ)):ℝ))).re
      - Real.sin ((-540841/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((68:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((68:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((68:ℕ)):ℝ)
      = ((((68:ℕ)):ℝ) * (Real.log (((68:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((68:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_68
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
  have hθwin : |(((-540841/1000000 : ℚ) : ℝ) + ((8:ℤ)) * (2*Real.pi) - Real.pi) - theta (((68:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((68:ℕ)):ℝ))
    (φ := ((-540841/1000000 : ℚ) : ℝ) + ((8:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-540841/1000000 : ℚ) : ℝ) + ((8:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-540841/1000000 : ℚ)) : ℝ) - Real.pi) + ((8:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-540841/1000000 : ℚ)) : ℝ) - Real.pi) 8).1,
    (cos_sin_shift ((((-540841/1000000 : ℚ)) : ℝ) - Real.pi) 8).2]
  exact cos_sin_flip ((-540841/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_68_sign
end AxiomAudit
