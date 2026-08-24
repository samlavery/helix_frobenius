import RequestProject.DVPSqrtTable

/-!
# Station `t = 74` of the extended Hardy ladder (rung-74)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT74 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((74 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((56183/125000 : ℚ) : ℝ))

theorem st74_c1 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((22517/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56183/500000) (δ := 1/100000000) (ψ := 56183/125000) 74 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t1 : ((90063/100000 : ℚ) : ℝ) ≤ stT74 1 := by
  have hc : ((90063/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90063/100000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((90063/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c2 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((837587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 722431/5000000) (δ := 587/100000000) (ψ := 56183/125000) 74 8
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t2 : ((5922280241979/10000000000000 : ℚ) : ℝ) ≤ stT74 2 := by
  have hc : ((837537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5922280241979/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((837537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c3 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((672241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -208391/1000000) (δ := 621/100000000) (ψ := 56183/125000) 74 13
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t3 : ((1940448041441/5000000000000 : ℚ) : ℝ) ≤ stT74 3 := by
  have hc : ((672191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1940448041441/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((672191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c4 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-691/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 501673/1250000) (δ := 433/100000000) (ψ := 56183/125000) 74 16
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t4 : ((-865000173/50000000000 : ℚ) : ℝ) ≤ stT74 4 := by
  have hc : ((-173/5000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-865000173/50000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-173/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c5 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((18603/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1828949/10000000) (δ := 339/50000000) (ψ := 56183/125000) 74 19
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t5 : ((66551629789/200000000000 : ℚ) : ℝ) ≤ stT74 5 := by
  have hc : ((74407/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((66551629789/200000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((74407/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c6 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((981271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 484613/10000000) (δ := 507/100000000) (ψ := 56183/125000) 74 21
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t6 : ((2002908535261/5000000000000 : ℚ) : ℝ) ≤ stT74 6 := by
  have hc : ((981221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2002908535261/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((981221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c7 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((142277/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1206719/5000000) (δ := 79/20000000) (ψ := 56183/125000) 74 23
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t7 : ((268854581919/1250000000000 : ℚ) : ℝ) ≤ stT74 7 := by
  have hc : ((284529/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268854581919/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((284529/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c8 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-174663/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3290953/5000000) (δ := 29/6250000) (ψ := 56183/125000) 74 24
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t8 : ((-308781165191/1000000000000 : ℚ) : ℝ) ≤ stT74 8 := by
  have hc : ((-174673/200000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-308781165191/1000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-174673/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c9 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((345839/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3044159/10000000) (δ := 27/5000000) (ψ := 56183/125000) 74 26
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t9 : ((1152629884737/10000000000000 : ℚ) : ℝ) ≤ stT74 9 := by
  have hc : ((345789/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1152629884737/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((345789/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c10 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((956561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 739573/10000000) (δ := 651/100000000) (ψ := 56183/125000) 74 27
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t10 : ((3024752735547/10000000000000 : ℚ) : ℝ) ≤ stT74 10 := by
  have hc : ((956511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3024752735547/10000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((956511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c11 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((241991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2663993/10000000) (δ := 251/50000000) (ψ := 56183/125000) 74 28
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t11 : ((364777416079/2500000000000 : ℚ) : ℝ) ≤ stT74 11 := by
  have hc : ((120983/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((364777416079/2500000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((120983/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c12 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((85617/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 610627/2000000) (δ := 391/100000000) (ψ := 56183/125000) 74 29
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t12 : ((494237751959/5000000000000 : ℚ) : ℝ) ≤ stT74 12 := by
  have hc : ((171209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((494237751959/5000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((171209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c13 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((130301/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2153073/10000000) (δ := 423/100000000) (ψ := 56183/125000) 74 30
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t13 : ((722724177/4000000000 : ℚ) : ℝ) ≤ stT74 13 := by
  have hc : ((130291/200000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((722724177/4000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((130291/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c14 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((998077/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 38771/2500000) (δ := 549/100000000) (ψ := 56183/125000) 74 31
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t14 : ((666834734131/2500000000000 : ℚ) : ℝ) ≤ stT74 14 := by
  have hc : ((998027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((666834734131/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((998027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c15 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((27473/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1394599/5000000) (δ := 759/100000000) (ψ := 56183/125000) 74 32
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t15 : ((141853775223/1250000000000 : ℚ) : ℝ) ≤ stT74 15 := by
  have hc : ((219759/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((141853775223/1250000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((219759/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c16 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-34741/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1311507/2000000) (δ := 19/3125000) (ψ := 56183/125000) 74 33
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t16 : ((-86857534743/400000000000 : ℚ) : ℝ) ≤ stT74 16 := by
  have hc : ((-34743/40000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86857534743/400000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-34743/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c17 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-144131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 232901/500000) (δ := 7/1562500) (ψ := 56183/125000) 74 33
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t17 : ((-87407440923/1250000000000 : ℚ) : ℝ) ≤ stT74 17 := by
  have hc : ((-36039/125000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87407440923/1250000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-36039/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c18 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((245489/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -118909/2500000) (δ := 213/50000000) (ψ := 56183/125000) 74 34
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t18 : ((578593510983/2500000000000 : ℚ) : ℝ) ≤ stT74 18 := by
  have hc : ((490953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((578593510983/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((490953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c19 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-784363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1545291/2500000) (δ := 557/100000000) (ψ := 56183/125000) 74 35
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t19 : ((-899783679627/5000000000000 : ℚ) : ℝ) ≤ stT74 19 := by
  have hc : ((-784413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-899783679627/5000000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-784413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c20 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((245037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 51689/156250) (δ := 537/100000000) (ψ := 56183/125000) 74 35
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t20 : ((547807346129/10000000000000 : ℚ) : ℝ) ≤ stT74 20 := by
  have hc : ((244987/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((547807346129/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((244987/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c21 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((219519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3373687/10000000) (δ := 119/25000000) (ψ := 56183/125000) 74 36
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t21 : ((239460211741/5000000000000 : ℚ) : ℝ) ≤ stT74 21 := by
  have hc : ((219469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239460211741/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((219469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c22 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-498797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1308129/2500000) (δ := 387/100000000) (ψ := 56183/125000) 74 36
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t22 : ((-132943224347/1250000000000 : ℚ) : ℝ) ≤ stT74 22 := by
  have hc : ((-498847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132943224347/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-498847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c23 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((19407/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2251871/10000000) (δ := 1/160000) (ψ := 56183/125000) 74 37
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t23 : ((80926263141/625000000000 : ℚ) : ℝ) ≤ stT74 23 := by
  have hc : ((310487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80926263141/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((310487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c24 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-627133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5621657/10000000) (δ := 109/20000000) (ψ := 56183/125000) 74 37
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t24 : ((-640116140643/5000000000000 : ℚ) : ℝ) ≤ stT74 24 := by
  have hc : ((-627183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-640116140643/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-627183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c25 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((66091/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2534237/10000000) (δ := 287/50000000) (ψ := 56183/125000) 74 38
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t25 : ((264339/2500000 : ℚ) : ℝ) ≤ stT74 25 := by
  have hc : ((264339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((264339/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((264339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c26 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-312517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 944319/2000000) (δ := 237/50000000) (ψ := 56183/125000) 74 38
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t26 : ((-306497261427/5000000000000 : ℚ) : ℝ) ≤ stT74 26 := by
  have hc : ((-312567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-306497261427/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-312567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c27 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-15481/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -500551/1250000) (δ := 23/5000000) (ψ := 56183/125000) 74 39
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t27 : ((-14920656253/2500000000000 : ℚ) : ℝ) ≤ stT74 27 := by
  have hc : ((-7753/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14920656253/2500000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-7753/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c28 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((23149/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1361803/5000000) (δ := 703/100000000) (ψ := 56183/125000) 74 39
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t28 : ((43742764923/500000000000 : ℚ) : ℝ) ≤ stT74 28 := by
  have hc : ((46293/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43742764923/500000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((46293/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c29 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-855331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6492463/10000000) (δ := 553/100000000) (ψ := 56183/125000) 74 40
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t29 : ((-794201584737/5000000000000 : ℚ) : ℝ) ≤ stT74 29 := by
  have hc : ((-855381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-794201584737/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-855381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c30 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((996107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -55169/2500000) (δ := 57/10000000) (ψ := 56183/125000) 74 40
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t30 : ((1818542103237/10000000000000 : ℚ) : ℝ) ≤ stT74 30 := by
  have hc : ((996057/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1818542103237/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((996057/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c31 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-173563/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2922721/5000000) (δ := 713/100000000) (ψ := 56183/125000) 74 40
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t31 : ((-311750971077/2500000000000 : ℚ) : ℝ) ≤ stT74 31 := by
  have hc : ((-347151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-311750971077/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-347151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c32 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-12403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -997253/2500000) (δ := 361/50000000) (ψ := 56183/125000) 74 41
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t32 : ((-5492452069/1250000000000 : ℚ) : ℝ) ≤ stT74 32 := by
  have hc : ((-3107/125000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5492452069/1250000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-3107/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c33 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((77663/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 26621/156250) (δ := 421/100000000) (ψ := 56183/125000) 74 41
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t33 : ((8449073913/62500000000 : ℚ) : ℝ) ≤ stT74 33 := by
  have hc : ((38829/50000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8449073913/62500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((38829/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c34 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-968671/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7226543/10000000) (δ := 281/50000000) (ψ := 56183/125000) 74 41
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t34 : ((-830671476453/5000000000000 : ℚ) : ℝ) ≤ stT74 34 := by
  have hc : ((-968721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-830671476453/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-968721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c35 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((317703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1559363/5000000) (δ := 113/25000000) (ψ := 56183/125000) 74 42
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t35 : ((134232851781/2500000000000 : ℚ) : ℝ) ≤ stT74 35 := by
  have hc : ((317653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134232851781/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((317653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c36 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((669579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1046443/5000000) (δ := 471/100000000) (ψ := 56183/125000) 74 42
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t36 : ((557940610157/5000000000000 : ℚ) : ℝ) ≤ stT74 36 := by
  have hc : ((669529/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((557940610157/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((669529/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c37 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-60119/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 223803/312500) (δ := 671/100000000) (ψ := 56183/125000) 74 42
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t37 : ((-79072137823/500000000000 : ℚ) : ℝ) ≤ stT74 37 := by
  have hc : ((-480977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79072137823/500000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-480977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c38 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((125409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3612641/10000000) (δ := 221/50000000) (ψ := 56183/125000) 74 43
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t38 : ((101679562413/5000000000000 : ℚ) : ℝ) ≤ stT74 38 := by
  have hc : ((125359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((101679562413/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((125359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c39 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((888317/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 149103/1250000) (δ := 401/100000000) (ψ := 56183/125000) 74 43
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t39 : ((1422365070027/10000000000000 : ℚ) : ℝ) ≤ stT74 39 := by
  have hc : ((888267/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1422365070027/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((888267/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c40 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-703173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2938309/5000000) (δ := 191/50000000) (ψ := 56183/125000) 74 43
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t40 : ((-1111893310997/10000000000000 : ℚ) : ℝ) ≤ stT74 40 := by
  have hc : ((-703223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1111893310997/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-703223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c41 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-509401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1315803/2500000) (δ := 473/100000000) (ψ := 56183/125000) 74 44
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t41 : ((-397814492919/5000000000000 : ℚ) : ℝ) ≤ stT74 41 := by
  have hc : ((-509451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-397814492919/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-509451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c42 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((948583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161033/2000000) (δ := 63/10000000) (ψ := 56183/125000) 74 44
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t42 : ((1463617720589/10000000000000 : ℚ) : ℝ) ≤ stT74 42 := by
  have hc : ((948533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1463617720589/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((948533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c43 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((6041/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3547977/10000000) (δ := 13/2000000) (ψ := 56183/125000) 74 44
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t43 : ((1841876883/80000000000 : ℚ) : ℝ) ≤ stT74 43 := by
  have hc : ((6039/40000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1841876883/80000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((6039/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c44 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-31243/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3900519/5000000) (δ := 51/10000000) (ψ := 56183/125000) 74 44
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t44 : ((-753647342541/5000000000000 : ℚ) : ℝ) ≤ stT74 44 := by
  have hc : ((-499913/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-753647342541/5000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-499913/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c45 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((35479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3749447/10000000) (δ := 161/25000000) (ψ := 56183/125000) 74 45
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t45 : ((26425833897/2500000000000 : ℚ) : ℝ) ≤ stT74 45 := by
  have hc : ((17727/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26425833897/2500000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((17727/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c46 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((991989/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 316651/10000000) (δ := 11/1562500) (ψ := 56183/125000) 74 45
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t46 : ((1462533708441/10000000000000 : ℚ) : ℝ) ≤ stT74 46 := by
  have hc : ((991939/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1462533708441/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((991939/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c47 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-146791/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4295299/10000000) (δ := 739/100000000) (ψ := 56183/125000) 74 45
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t47 : ((-4283792493/200000000000 : ℚ) : ℝ) ≤ stT74 47 := by
  have hc : ((-146841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4283792493/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-146841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c48 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-990971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -939723/1250000) (δ := 43/6250000) (ψ := 56183/125000) 74 46
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t48 : ((-89400995431/625000000000 : ℚ) : ℝ) ≤ stT74 48 := by
  have hc : ((-991021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89400995431/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-991021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c49 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((8939/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231451/625000) (δ := 139/20000000) (ψ := 56183/125000) 74 46
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t49 : ((6381426657/500000000000 : ℚ) : ℝ) ≤ stT74 49 := by
  have hc : ((4467/50000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6381426657/500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((4467/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c50 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((499953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6857/2000000) (δ := 91/12500000) (ψ := 56183/125000) 74 46
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t50 : ((88375584583/625000000000 : ℚ) : ℝ) ≤ stT74 50 := by
  have hc : ((62491/62500 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88375584583/625000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((62491/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c51 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((2289/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3697771/10000000) (δ := 33/6250000) (ψ := 56183/125000) 74 46
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t51 : ((320349057/25000000000 : ℚ) : ℝ) ≤ stT74 51 := by
  have hc : ((9151/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((320349057/25000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((9151/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c52 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-60917/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7290117/10000000) (δ := 157/25000000) (ψ := 56183/125000) 74 46
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t52 : ((-675848354111/5000000000000 : ℚ) : ℝ) ≤ stT74 52 := by
  have hc : ((-487361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-675848354111/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-487361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c53 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-94301/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -489393/1000000) (δ := 329/50000000) (ψ := 56183/125000) 74 47
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t53 : ((-129549589481/2500000000000 : ℚ) : ℝ) ≤ stT74 53 := by
  have hc : ((-188627/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129549589481/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-188627/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c54 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((839543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -287177/2000000) (δ := 199/50000000) (ψ := 56183/125000) 74 47
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t54 : ((1142404740711/10000000000000 : ℚ) : ℝ) ≤ stT74 54 := by
  have hc : ((839493/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1142404740711/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((839493/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c55 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((35423/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 391741/2000000) (δ := 121/20000000) (ψ := 56183/125000) 74 47
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t55 : ((95521933559/1000000000000 : ℚ) : ℝ) ≤ stT74 55 := by
  have hc : ((70841/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95521933559/1000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((70841/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c56 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-12983/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5292129/10000000) (δ := 133/20000000) (ψ := 56183/125000) 74 47
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t56 : ((-69403776659/1000000000000 : ℚ) : ℝ) ≤ stT74 56 := by
  have hc : ((-51937/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69403776659/1000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-51937/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c57 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-479827/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7141413/10000000) (δ := 119/25000000) (ψ := 56183/125000) 74 48
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t57 : ((-158894952279/1250000000000 : ℚ) : ℝ) ≤ stT74 57 := by
  have hc : ((-119963/125000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-158894952279/1250000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-119963/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c58 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((61/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196197/500000) (δ := 667/100000000) (ψ := 56183/125000) 74 48
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t58 : ((19203561/125000000000 : ℚ) : ℝ) ≤ stT74 58 := by
  have hc : ((117/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19203561/125000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((117/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c59 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((953971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76147/1000000) (δ := 427/100000000) (ψ := 56183/125000) 74 48
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t59 : ((1241899256769/10000000000000 : ℚ) : ℝ) ≤ stT74 59 := by
  have hc : ((953921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1241899256769/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((953921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c60 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((590483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2347847/10000000) (δ := 57/12500000) (ψ := 56183/125000) 74 48
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t60 : ((381122730201/5000000000000 : ℚ) : ℝ) ≤ stT74 60 := by
  have hc : ((590433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((381122730201/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((590433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c61 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-34851/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 675721/1250000) (δ := 119/25000000) (ψ := 56183/125000) 74 48
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t61 : ((-357009129377/5000000000000 : ℚ) : ℝ) ≤ stT74 61 := by
  have hc : ((-278833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-357009129377/5000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-278833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c62 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-487509/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7293999/10000000) (δ := 627/100000000) (ψ := 56183/125000) 74 49
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t62 : ((-154792288767/1250000000000 : ℚ) : ℝ) ≤ stT74 62 := by
  have hc : ((-243767/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154792288767/1250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-243767/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c63 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-8103/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270871/625000) (δ := 139/25000000) (ψ := 56183/125000) 74 49
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t63 : ((-10211973551/500000000000 : ℚ) : ℝ) ≤ stT74 63 := by
  have hc : ((-16211/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10211973551/500000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-16211/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c64 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((842873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -142049/1000000) (δ := 607/100000000) (ψ := 56183/125000) 74 49
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t64 : ((842823/8000000 : ℚ) : ℝ) ≤ stT74 64 := by
  have hc : ((842823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((842823/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((842823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c65 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((209237/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180973/1250000) (δ := 487/100000000) (ψ := 56183/125000) 74 49
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t65 : ((519021961803/5000000000000 : ℚ) : ℝ) ≤ stT74 65 := by
  have hc : ((418449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((519021961803/5000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((418449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c66 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-17209/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4272267/10000000) (δ := 109/25000000) (ψ := 56183/125000) 74 49
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t66 : ((-16952407563/1000000000000 : ℚ) : ℝ) ≤ stT74 66 := by
  have hc : ((-68861/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16952407563/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-68861/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c67 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-118659/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3527137/5000000) (δ := 77/12500000) (ψ := 56183/125000) 74 49
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t67 : ((-115978194079/1000000000000 : ℚ) : ℝ) ≤ stT74 67 := by
  have hc : ((-474661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115978194079/1000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-474661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c68 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-713417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2956449/5000000) (δ := 353/50000000) (ψ := 56183/125000) 74 50
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t68 : ((-865206448093/10000000000000 : ℚ) : ℝ) ≤ stT74 68 := by
  have hc : ((-713467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-865206448093/10000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-713467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c69 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((282067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3212121/10000000) (δ := 373/50000000) (ψ := 56183/125000) 74 50
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t69 : ((169754210793/5000000000000 : ℚ) : ℝ) ≤ stT74 69 := by
  have hc : ((282017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169754210793/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((282017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c70 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((24397/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -137551/2500000) (δ := 223/50000000) (ψ := 56183/125000) 74 50
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t70 : ((29158483481/250000000000 : ℚ) : ℝ) ≤ stT74 70 := by
  have hc : ((97583/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29158483481/250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((97583/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c71 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((135037/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2073953/10000000) (δ := 537/100000000) (ψ := 56183/125000) 74 50
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t71 : ((160247478087/2000000000000 : ℚ) : ℝ) ≤ stT74 71 := by
  have hc : ((135027/200000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160247478087/2000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((135027/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c72 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-7239/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145669/312500) (δ := 313/50000000) (ψ := 56183/125000) 74 50
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t72 : ((-2133180377/62500000000 : ℚ) : ℝ) ≤ stT74 72 := by
  have hc : ((-28961/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2133180377/62500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-28961/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c73 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-967329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7213173/10000000) (δ := 223/50000000) (ψ := 56183/125000) 74 50
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t73 : ((-283057997537/2500000000000 : ℚ) : ℝ) ≤ stT74 73 := by
  have hc : ((-967379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-283057997537/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-967379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c74 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-91419/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1195549/2000000) (δ := 167/25000000) (ψ := 56183/125000) 74 51
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t74 : ((-425119001377/5000000000000 : ℚ) : ℝ) ≤ stT74 74 := by
  have hc : ((-365701/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-425119001377/5000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-365701/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c75 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((8607/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1747243/5000000) (δ := 131/20000000) (ψ := 56183/125000) 74 51
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t75 : ((198712323/10000000000 : ℚ) : ℝ) ≤ stT74 75 := by
  have hc : ((17209/100000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198712323/10000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((17209/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c76 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((457023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1044119/10000000) (δ := 91/20000000) (ψ := 56183/125000) 74 51
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t76 : ((131053087961/1250000000000 : ℚ) : ℝ) ≤ stT74 76 := by
  have hc : ((228499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((131053087961/1250000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((228499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c77 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((53293/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 171777/1250000) (δ := 119/20000000) (ψ := 56183/125000) 74 51
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t77 : ((97167052799/1000000000000 : ℚ) : ℝ) ≤ stT74 77 := by
  have hc : ((426319/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((97167052799/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((426319/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c78 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((66209/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1880673/5000000) (δ := 111/20000000) (ψ := 56183/125000) 74 51
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t78 : ((74910314043/10000000000000 : ℚ) : ℝ) ≤ stT74 78 := by
  have hc : ((66159/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((74910314043/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((66159/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c79 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-768459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3059033/5000000) (δ := 97/25000000) (ψ := 56183/125000) 74 51
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t79 : ((-27020007931/312500000000 : ℚ) : ℝ) ≤ stT74 79 := by
  have hc : ((-768509/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27020007931/312500000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-768509/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c80 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-972173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7262823/10000000) (δ := 63/12500000) (ψ := 56183/125000) 74 52
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t80 : ((-543489184791/5000000000000 : ℚ) : ℝ) ≤ stT74 80 := by
  have hc : ((-972223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-543489184791/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-972223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c81 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-403251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4964657/10000000) (δ := 379/100000000) (ψ := 56183/125000) 74 52
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t81 : ((-56014072589/1250000000000 : ℚ) : ℝ) ≤ stT74 81 := by
  have hc : ((-403301/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56014072589/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-403301/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c82 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((473201/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269469/1000000) (δ := 53/12500000) (ψ := 56183/125000) 74 52
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t82 : ((104501549313/2000000000000 : ℚ) : ℝ) ≤ stT74 82 := by
  have hc : ((473151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104501549313/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((473151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c83 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((983683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -226119/5000000) (δ := 11/1562500) (ψ := 56183/125000) 74 52
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t83 : ((539838446693/5000000000000 : ℚ) : ℝ) ≤ stT74 83 := by
  have hc : ((983633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539838446693/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((983633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c84 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((761389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1763357/10000000) (δ := 49/6250000) (ψ := 56183/125000) 74 52
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t84 : ((830688608171/10000000000000 : ℚ) : ℝ) ≤ stT74 84 := by
  have hc : ((761339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((830688608171/10000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((761339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c85 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-1287/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 988183/2500000) (δ := 399/100000000) (ψ := 56183/125000) 74 52
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t85 : ((-5610909969/5000000000000 : ℚ) : ℝ) ≤ stT74 85 := by
  have hc : ((-5173/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5610909969/5000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-5173/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c86 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-384029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6116499/10000000) (δ := 679/100000000) (ψ := 56183/125000) 74 52
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t86 : ((-25883511357/312500000000 : ℚ) : ℝ) ≤ stT74 86 := by
  have hc : ((-192027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25883511357/312500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-192027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c87 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-493573/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -931589/1250000) (δ := 633/100000000) (ψ := 56183/125000) 74 53
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t87 : ((-264596416287/2500000000000 : ℚ) : ℝ) ≤ stT74 87 := by
  have hc : ((-246799/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-264596416287/2500000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-246799/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c88 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-66881/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5338403/10000000) (δ := 653/100000000) (ψ := 56183/125000) 74 53
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t88 : ((-71302076049/1250000000000 : ℚ) : ℝ) ≤ stT74 88 := by
  have hc : ((-267549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71302076049/1250000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-267549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c89 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((10731/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -649597/2000000) (δ := 51/10000000) (ψ := 56183/125000) 74 53
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t89 : ((11372707813/400000000000 : ℚ) : ℝ) ≤ stT74 89 := by
  have hc : ((10729/40000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11372707813/400000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((10729/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c90 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((222623/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47237/400000) (δ := 49/10000000) (ψ := 56183/125000) 74 53
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t90 : ((117325973583/1250000000000 : ℚ) : ℝ) ≤ stT74 90 := by
  have hc : ((445221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117325973583/1250000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((445221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c91 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((117621/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 172659/2000000) (δ := 77/10000000) (ψ := 56183/125000) 74 53
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t91 : ((123293660589/1250000000000 : ℚ) : ℝ) ≤ stT74 91 := by
  have hc : ((470459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123293660589/1250000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((470459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c92 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((40477/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2885173/10000000) (δ := 11/2000000) (ψ := 56183/125000) 74 53
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t92 : ((1318592937/31250000000 : ℚ) : ℝ) ≤ stT74 92 := by
  have hc : ((5059/12500 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1318592937/31250000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((5059/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c93 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-74793/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4885193/10000000) (δ := 69/10000000) (ψ := 56183/125000) 74 53
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t93 : ((-9695890057/250000000000 : ℚ) : ℝ) ≤ stT74 93 := by
  have hc : ((-74803/200000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9695890057/250000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-74803/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c94 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-922587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6863821/10000000) (δ := 59/10000000) (ψ := 56183/125000) 74 53
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t94 : ((-475814049907/5000000000000 : ℚ) : ℝ) ≤ stT74 94 := by
  have hc : ((-922637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-475814049907/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-922637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c95 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-926041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1721613/2500000) (δ := 33/5000000) (ψ := 56183/125000) 74 54
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t95 : ((-950149918089/10000000000000 : ℚ) : ℝ) ≤ stT74 95 := by
  have hc : ((-926091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-950149918089/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-926091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c96 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((-49701/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2474631/5000000) (δ := 1/156250) (ψ := 56183/125000) 74 54
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t96 : ((-202929052809/5000000000000 : ℚ) : ℝ) ≤ stT74 96 := by
  have hc : ((-198829/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202929052809/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-198829/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c97 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((43793/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1516073/5000000) (δ := 7/1250000) (ψ := 56183/125000) 74 54
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t97 : ((88917402931/2500000000000 : ℚ) : ℝ) ≤ stT74 97 := by
  have hc : ((175147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88917402931/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((175147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c98 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((449377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1134693/10000000) (δ := 29/5000000) (ψ := 56183/125000) 74 54
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t98 : ((7092403461/78125000000 : ℚ) : ℝ) ≤ stT74 98 := by
  have hc : ((56169/62500 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7092403461/78125000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((56169/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c99 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((478051/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 148699/2000000) (δ := 403/100000000) (ψ := 56183/125000) 74 54
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t99 : ((240216908481/2500000000000 : ℚ) : ℝ) ≤ stT74 99 := by
  have hc : ((239013/250000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240216908481/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((239013/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_c100 :
    |Real.cos (((74 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((56183/125000 : ℚ) : ℝ))
      - ((126313/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2602807/10000000) (δ := 3/500000) (ψ := 56183/125000) 74 54
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st74_t100 : ((252600747399/5000000000000 : ℚ) : ℝ) ≤ stT74 100 := by
  have hc : ((252601/500000 : ℚ) : ℝ)
      ≤ Real.cos (((74 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((56183/125000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st74_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252600747399/5000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((252601/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st74_p1 : ((90063/100000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT74 (i+1) := by
  rw [Finset.sum_range_one]
  exact st74_t1

theorem st74_p2 : ((14928580241979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT74 (i+1))
      = (∑ i ∈ Finset.range 1, stT74 (i+1)) + stT74 2 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 1
    simpa using h
  have hprev := st74_p1
  have hstep := st74_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p3 : ((18809476324861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT74 (i+1))
      = (∑ i ∈ Finset.range 2, stT74 (i+1)) + stT74 3 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 2
    simpa using h
  have hprev := st74_p2
  have hstep := st74_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p4 : ((18636476290261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT74 (i+1))
      = (∑ i ∈ Finset.range 3, stT74 (i+1)) + stT74 4 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 3
    simpa using h
  have hprev := st74_p3
  have hstep := st74_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p5 : ((21964057779711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT74 (i+1))
      = (∑ i ∈ Finset.range 4, stT74 (i+1)) + stT74 5 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 4
    simpa using h
  have hprev := st74_p4
  have hstep := st74_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p6 : ((25969874850233/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT74 (i+1))
      = (∑ i ∈ Finset.range 5, stT74 (i+1)) + stT74 6 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 5
    simpa using h
  have hprev := st74_p5
  have hstep := st74_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p7 : ((5624142301117/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT74 (i+1))
      = (∑ i ∈ Finset.range 6, stT74 (i+1)) + stT74 7 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 6
    simpa using h
  have hprev := st74_p6
  have hstep := st74_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p8 : ((1001315994147/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT74 (i+1))
      = (∑ i ∈ Finset.range 7, stT74 (i+1)) + stT74 8 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 7
    simpa using h
  have hprev := st74_p7
  have hstep := st74_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p9 : ((6546382434603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT74 (i+1))
      = (∑ i ∈ Finset.range 8, stT74 (i+1)) + stT74 9 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 8
    simpa using h
  have hprev := st74_p8
  have hstep := st74_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p10 : ((29210282473959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT74 (i+1))
      = (∑ i ∈ Finset.range 9, stT74 (i+1)) + stT74 10 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 9
    simpa using h
  have hprev := st74_p9
  have hstep := st74_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p11 : ((1226775685531/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT74 (i+1))
      = (∑ i ∈ Finset.range 10, stT74 (i+1)) + stT74 11 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 10
    simpa using h
  have hprev := st74_p10
  have hstep := st74_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p12 : ((31657867642193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT74 (i+1))
      = (∑ i ∈ Finset.range 11, stT74 (i+1)) + stT74 12 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 11
    simpa using h
  have hprev := st74_p11
  have hstep := st74_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p13 : ((33464678084693/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT74 (i+1))
      = (∑ i ∈ Finset.range 12, stT74 (i+1)) + stT74 13 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 12
    simpa using h
  have hprev := st74_p12
  have hstep := st74_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p14 : ((36132017021217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT74 (i+1))
      = (∑ i ∈ Finset.range 13, stT74 (i+1)) + stT74 14 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 13
    simpa using h
  have hprev := st74_p13
  have hstep := st74_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p15 : ((37266847223001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT74 (i+1))
      = (∑ i ∈ Finset.range 14, stT74 (i+1)) + stT74 15 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 14
    simpa using h
  have hprev := st74_p14
  have hstep := st74_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p16 : ((17547704427213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT74 (i+1))
      = (∑ i ∈ Finset.range 15, stT74 (i+1)) + stT74 16 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 15
    simpa using h
  have hprev := st74_p15
  have hstep := st74_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p17 : ((17198074663521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT74 (i+1))
      = (∑ i ∈ Finset.range 16, stT74 (i+1)) + stT74 17 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 16
    simpa using h
  have hprev := st74_p16
  have hstep := st74_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p18 : ((18355261685487/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT74 (i+1))
      = (∑ i ∈ Finset.range 17, stT74 (i+1)) + stT74 18 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 17
    simpa using h
  have hprev := st74_p17
  have hstep := st74_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p19 : ((872773900293/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT74 (i+1))
      = (∑ i ∈ Finset.range 18, stT74 (i+1)) + stT74 19 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 18
    simpa using h
  have hprev := st74_p18
  have hstep := st74_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p20 : ((35458763357849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT74 (i+1))
      = (∑ i ∈ Finset.range 19, stT74 (i+1)) + stT74 20 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 19
    simpa using h
  have hprev := st74_p19
  have hstep := st74_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p21 : ((35937683781331/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT74 (i+1))
      = (∑ i ∈ Finset.range 20, stT74 (i+1)) + stT74 21 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 20
    simpa using h
  have hprev := st74_p20
  have hstep := st74_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p22 : ((6974827597311/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT74 (i+1))
      = (∑ i ∈ Finset.range 21, stT74 (i+1)) + stT74 22 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 21
    simpa using h
  have hprev := st74_p21
  have hstep := st74_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p23 : ((36168958196811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT74 (i+1))
      = (∑ i ∈ Finset.range 22, stT74 (i+1)) + stT74 23 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 22
    simpa using h
  have hprev := st74_p22
  have hstep := st74_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p24 : ((1395549036621/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT74 (i+1))
      = (∑ i ∈ Finset.range 23, stT74 (i+1)) + stT74 24 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 23
    simpa using h
  have hprev := st74_p23
  have hstep := st74_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p25 : ((1437843276621/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT74 (i+1))
      = (∑ i ∈ Finset.range 24, stT74 (i+1)) + stT74 25 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 24
    simpa using h
  have hprev := st74_p24
  have hstep := st74_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p26 : ((35333087392671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT74 (i+1))
      = (∑ i ∈ Finset.range 25, stT74 (i+1)) + stT74 26 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 25
    simpa using h
  have hprev := st74_p25
  have hstep := st74_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p27 : ((35273404767659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT74 (i+1))
      = (∑ i ∈ Finset.range 26, stT74 (i+1)) + stT74 27 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 26
    simpa using h
  have hprev := st74_p26
  have hstep := st74_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p28 : ((36148260066119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT74 (i+1))
      = (∑ i ∈ Finset.range 27, stT74 (i+1)) + stT74 28 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 27
    simpa using h
  have hprev := st74_p27
  have hstep := st74_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p29 : ((6911971379329/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT74 (i+1))
      = (∑ i ∈ Finset.range 28, stT74 (i+1)) + stT74 29 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 28
    simpa using h
  have hprev := st74_p28
  have hstep := st74_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p30 : ((18189199499941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT74 (i+1))
      = (∑ i ∈ Finset.range 29, stT74 (i+1)) + stT74 30 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 29
    simpa using h
  have hprev := st74_p29
  have hstep := st74_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p31 : ((17565697557787/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT74 (i+1))
      = (∑ i ∈ Finset.range 30, stT74 (i+1)) + stT74 31 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 30
    simpa using h
  have hprev := st74_p30
  have hstep := st74_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p32 : ((17543727749511/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT74 (i+1))
      = (∑ i ∈ Finset.range 31, stT74 (i+1)) + stT74 32 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 31
    simpa using h
  have hprev := st74_p31
  have hstep := st74_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p33 : ((18219653662551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT74 (i+1))
      = (∑ i ∈ Finset.range 32, stT74 (i+1)) + stT74 33 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 32
    simpa using h
  have hprev := st74_p32
  have hstep := st74_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p34 : ((8694491093049/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT74 (i+1))
      = (∑ i ∈ Finset.range 33, stT74 (i+1)) + stT74 34 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 33
    simpa using h
  have hprev := st74_p33
  have hstep := st74_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p35 : ((882872394483/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT74 (i+1))
      = (∑ i ∈ Finset.range 34, stT74 (i+1)) + stT74 35 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 34
    simpa using h
  have hprev := st74_p34
  have hstep := st74_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p36 : ((18215388499817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT74 (i+1))
      = (∑ i ∈ Finset.range 35, stT74 (i+1)) + stT74 36 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 35
    simpa using h
  have hprev := st74_p35
  have hstep := st74_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p37 : ((17424667121587/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT74 (i+1))
      = (∑ i ∈ Finset.range 36, stT74 (i+1)) + stT74 37 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 36
    simpa using h
  have hprev := st74_p36
  have hstep := st74_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p38 : ((4381586671/1250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT74 (i+1))
      = (∑ i ∈ Finset.range 37, stT74 (i+1)) + stT74 38 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 37
    simpa using h
  have hprev := st74_p37
  have hstep := st74_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p39 : ((36475058438027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT74 (i+1))
      = (∑ i ∈ Finset.range 38, stT74 (i+1)) + stT74 39 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 38
    simpa using h
  have hprev := st74_p38
  have hstep := st74_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p40 : ((3536316512703/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT74 (i+1))
      = (∑ i ∈ Finset.range 39, stT74 (i+1)) + stT74 40 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 39
    simpa using h
  have hprev := st74_p39
  have hstep := st74_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p41 : ((4320942017649/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT74 (i+1))
      = (∑ i ∈ Finset.range 40, stT74 (i+1)) + stT74 41 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 40
    simpa using h
  have hprev := st74_p40
  have hstep := st74_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p42 : ((36031153861781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT74 (i+1))
      = (∑ i ∈ Finset.range 41, stT74 (i+1)) + stT74 42 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 41
    simpa using h
  have hprev := st74_p41
  have hstep := st74_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p43 : ((9065347118039/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT74 (i+1))
      = (∑ i ∈ Finset.range 42, stT74 (i+1)) + stT74 43 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 42
    simpa using h
  have hprev := st74_p42
  have hstep := st74_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p44 : ((17377046893537/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT74 (i+1))
      = (∑ i ∈ Finset.range 43, stT74 (i+1)) + stT74 44 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 43
    simpa using h
  have hprev := st74_p43
  have hstep := st74_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p45 : ((17429898561331/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT74 (i+1))
      = (∑ i ∈ Finset.range 44, stT74 (i+1)) + stT74 45 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 44
    simpa using h
  have hprev := st74_p44
  have hstep := st74_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p46 : ((36322330831103/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT74 (i+1))
      = (∑ i ∈ Finset.range 45, stT74 (i+1)) + stT74 46 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 45
    simpa using h
  have hprev := st74_p45
  have hstep := st74_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p47 : ((36108141206453/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT74 (i+1))
      = (∑ i ∈ Finset.range 46, stT74 (i+1)) + stT74 47 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 46
    simpa using h
  have hprev := st74_p46
  have hstep := st74_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p48 : ((34677725279557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT74 (i+1))
      = (∑ i ∈ Finset.range 47, stT74 (i+1)) + stT74 48 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 47
    simpa using h
  have hprev := st74_p47
  have hstep := st74_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p49 : ((34805353812697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT74 (i+1))
      = (∑ i ∈ Finset.range 48, stT74 (i+1)) + stT74 49 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 48
    simpa using h
  have hprev := st74_p48
  have hstep := st74_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p50 : ((1448774526641/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT74 (i+1))
      = (∑ i ∈ Finset.range 49, stT74 (i+1)) + stT74 50 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 49
    simpa using h
  have hprev := st74_p49
  have hstep := st74_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p51 : ((1453900111553/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT74 (i+1))
      = (∑ i ∈ Finset.range 50, stT74 (i+1)) + stT74 51 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 50
    simpa using h
  have hprev := st74_p50
  have hstep := st74_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p52 : ((34995806080603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT74 (i+1))
      = (∑ i ∈ Finset.range 51, stT74 (i+1)) + stT74 52 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 51
    simpa using h
  have hprev := st74_p51
  have hstep := st74_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p53 : ((34477607722679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT74 (i+1))
      = (∑ i ∈ Finset.range 52, stT74 (i+1)) + stT74 53 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 52
    simpa using h
  have hprev := st74_p52
  have hstep := st74_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p54 : ((3562001246339/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT74 (i+1))
      = (∑ i ∈ Finset.range 53, stT74 (i+1)) + stT74 54 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 53
    simpa using h
  have hprev := st74_p53
  have hstep := st74_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p55 : ((1828761589949/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT74 (i+1))
      = (∑ i ∈ Finset.range 54, stT74 (i+1)) + stT74 55 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 54
    simpa using h
  have hprev := st74_p54
  have hstep := st74_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p56 : ((3588119403239/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT74 (i+1))
      = (∑ i ∈ Finset.range 55, stT74 (i+1)) + stT74 56 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 55
    simpa using h
  have hprev := st74_p55
  have hstep := st74_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p57 : ((17305017207079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT74 (i+1))
      = (∑ i ∈ Finset.range 56, stT74 (i+1)) + stT74 57 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 56
    simpa using h
  have hprev := st74_p56
  have hstep := st74_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p58 : ((17305785349519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT74 (i+1))
      = (∑ i ∈ Finset.range 57, stT74 (i+1)) + stT74 58 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 57
    simpa using h
  have hprev := st74_p57
  have hstep := st74_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p59 : ((35853469955807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT74 (i+1))
      = (∑ i ∈ Finset.range 58, stT74 (i+1)) + stT74 59 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 58
    simpa using h
  have hprev := st74_p58
  have hstep := st74_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p60 : ((36615715416209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT74 (i+1))
      = (∑ i ∈ Finset.range 59, stT74 (i+1)) + stT74 60 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 59
    simpa using h
  have hprev := st74_p59
  have hstep := st74_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p61 : ((7180339431491/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT74 (i+1))
      = (∑ i ∈ Finset.range 60, stT74 (i+1)) + stT74 61 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 60
    simpa using h
  have hprev := st74_p60
  have hstep := st74_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p62 : ((34663358847319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT74 (i+1))
      = (∑ i ∈ Finset.range 61, stT74 (i+1)) + stT74 62 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 61
    simpa using h
  have hprev := st74_p61
  have hstep := st74_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p63 : ((34459119376299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT74 (i+1))
      = (∑ i ∈ Finset.range 62, stT74 (i+1)) + stT74 63 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 62
    simpa using h
  have hprev := st74_p62
  have hstep := st74_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p64 : ((35512648126299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT74 (i+1))
      = (∑ i ∈ Finset.range 63, stT74 (i+1)) + stT74 64 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 63
    simpa using h
  have hprev := st74_p63
  have hstep := st74_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p65 : ((7310138409981/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT74 (i+1))
      = (∑ i ∈ Finset.range 64, stT74 (i+1)) + stT74 65 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 64
    simpa using h
  have hprev := st74_p64
  have hstep := st74_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p66 : ((1455246718971/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT74 (i+1))
      = (∑ i ∈ Finset.range 65, stT74 (i+1)) + stT74 66 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 65
    simpa using h
  have hprev := st74_p65
  have hstep := st74_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p67 : ((7044277206697/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT74 (i+1))
      = (∑ i ∈ Finset.range 66, stT74 (i+1)) + stT74 67 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 66
    simpa using h
  have hprev := st74_p66
  have hstep := st74_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p68 : ((2147261224087/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT74 (i+1))
      = (∑ i ∈ Finset.range 67, stT74 (i+1)) + stT74 68 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 67
    simpa using h
  have hprev := st74_p67
  have hstep := st74_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p69 : ((17347844003489/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT74 (i+1))
      = (∑ i ∈ Finset.range 68, stT74 (i+1)) + stT74 69 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 68
    simpa using h
  have hprev := st74_p68
  have hstep := st74_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p70 : ((17931013673109/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT74 (i+1))
      = (∑ i ∈ Finset.range 69, stT74 (i+1)) + stT74 70 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 69
    simpa using h
  have hprev := st74_p69
  have hstep := st74_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p71 : ((36663264736653/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT74 (i+1))
      = (∑ i ∈ Finset.range 70, stT74 (i+1)) + stT74 71 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 70
    simpa using h
  have hprev := st74_p70
  have hstep := st74_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p72 : ((36321955876333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT74 (i+1))
      = (∑ i ∈ Finset.range 71, stT74 (i+1)) + stT74 72 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 71
    simpa using h
  have hprev := st74_p71
  have hstep := st74_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p73 : ((7037944777237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT74 (i+1))
      = (∑ i ∈ Finset.range 72, stT74 (i+1)) + stT74 73 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 72
    simpa using h
  have hprev := st74_p72
  have hstep := st74_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p74 : ((34339485883431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT74 (i+1))
      = (∑ i ∈ Finset.range 73, stT74 (i+1)) + stT74 74 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 73
    simpa using h
  have hprev := st74_p73
  have hstep := st74_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p75 : ((34538198206431/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT74 (i+1))
      = (∑ i ∈ Finset.range 74, stT74 (i+1)) + stT74 75 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 74
    simpa using h
  have hprev := st74_p74
  have hstep := st74_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p76 : ((35586622910119/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT74 (i+1))
      = (∑ i ∈ Finset.range 75, stT74 (i+1)) + stT74 76 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 75
    simpa using h
  have hprev := st74_p75
  have hstep := st74_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p77 : ((36558293438109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT74 (i+1))
      = (∑ i ∈ Finset.range 76, stT74 (i+1)) + stT74 77 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 76
    simpa using h
  have hprev := st74_p76
  have hstep := st74_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p78 : ((4579150469019/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT74 (i+1))
      = (∑ i ∈ Finset.range 77, stT74 (i+1)) + stT74 78 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 77
    simpa using h
  have hprev := st74_p77
  have hstep := st74_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p79 : ((894214087459/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT74 (i+1))
      = (∑ i ∈ Finset.range 78, stT74 (i+1)) + stT74 79 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 78
    simpa using h
  have hprev := st74_p78
  have hstep := st74_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p80 : ((17340792564389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT74 (i+1))
      = (∑ i ∈ Finset.range 79, stT74 (i+1)) + stT74 80 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 79
    simpa using h
  have hprev := st74_p79
  have hstep := st74_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p81 : ((17116736274033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT74 (i+1))
      = (∑ i ∈ Finset.range 80, stT74 (i+1)) + stT74 81 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 80
    simpa using h
  have hprev := st74_p80
  have hstep := st74_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p82 : ((34755980294631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT74 (i+1))
      = (∑ i ∈ Finset.range 81, stT74 (i+1)) + stT74 82 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 81
    simpa using h
  have hprev := st74_p81
  have hstep := st74_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p83 : ((35835657188017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT74 (i+1))
      = (∑ i ∈ Finset.range 82, stT74 (i+1)) + stT74 83 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 82
    simpa using h
  have hprev := st74_p82
  have hstep := st74_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p84 : ((9166586449047/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT74 (i+1))
      = (∑ i ∈ Finset.range 83, stT74 (i+1)) + stT74 84 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 83
    simpa using h
  have hprev := st74_p83
  have hstep := st74_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p85 : ((29324099181/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT74 (i+1))
      = (∑ i ∈ Finset.range 84, stT74 (i+1)) + stT74 85 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 84
    simpa using h
  have hprev := st74_p84
  have hstep := st74_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p86 : ((17913425806413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT74 (i+1))
      = (∑ i ∈ Finset.range 85, stT74 (i+1)) + stT74 86 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 85
    simpa using h
  have hprev := st74_p85
  have hstep := st74_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p87 : ((17384232973839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT74 (i+1))
      = (∑ i ∈ Finset.range 86, stT74 (i+1)) + stT74 87 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 86
    simpa using h
  have hprev := st74_p86
  have hstep := st74_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p88 : ((17099024669643/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT74 (i+1))
      = (∑ i ∈ Finset.range 87, stT74 (i+1)) + stT74 88 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 87
    simpa using h
  have hprev := st74_p87
  have hstep := st74_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p89 : ((34482367034611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT74 (i+1))
      = (∑ i ∈ Finset.range 88, stT74 (i+1)) + stT74 89 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 88
    simpa using h
  have hprev := st74_p88
  have hstep := st74_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p90 : ((1416838992931/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT74 (i+1))
      = (∑ i ∈ Finset.range 89, stT74 (i+1)) + stT74 90 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 89
    simpa using h
  have hprev := st74_p89
  have hstep := st74_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p91 : ((36407324107987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT74 (i+1))
      = (∑ i ∈ Finset.range 90, stT74 (i+1)) + stT74 91 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 90
    simpa using h
  have hprev := st74_p90
  have hstep := st74_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p92 : ((36829273847827/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT74 (i+1))
      = (∑ i ∈ Finset.range 91, stT74 (i+1)) + stT74 92 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 91
    simpa using h
  have hprev := st74_p91
  have hstep := st74_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p93 : ((36441438245547/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT74 (i+1))
      = (∑ i ∈ Finset.range 92, stT74 (i+1)) + stT74 93 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 92
    simpa using h
  have hprev := st74_p92
  have hstep := st74_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p94 : ((35489810145733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT74 (i+1))
      = (∑ i ∈ Finset.range 93, stT74 (i+1)) + stT74 94 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 93
    simpa using h
  have hprev := st74_p93
  have hstep := st74_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p95 : ((8634915056911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT74 (i+1))
      = (∑ i ∈ Finset.range 94, stT74 (i+1)) + stT74 95 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 94
    simpa using h
  have hprev := st74_p94
  have hstep := st74_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p96 : ((17066901061013/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT74 (i+1))
      = (∑ i ∈ Finset.range 95, stT74 (i+1)) + stT74 96 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 95
    simpa using h
  have hprev := st74_p95
  have hstep := st74_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p97 : ((27591577387/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT74 (i+1))
      = (∑ i ∈ Finset.range 96, stT74 (i+1)) + stT74 97 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 96
    simpa using h
  have hprev := st74_p96
  have hstep := st74_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p98 : ((17698649688379/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT74 (i+1))
      = (∑ i ∈ Finset.range 97, stT74 (i+1)) + stT74 98 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 97
    simpa using h
  have hprev := st74_p97
  have hstep := st74_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p99 : ((18179083505341/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT74 (i+1))
      = (∑ i ∈ Finset.range 98, stT74 (i+1)) + stT74 99 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 98
    simpa using h
  have hprev := st74_p98
  have hstep := st74_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st74_p100 : ((921584212637/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT74 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT74 (i+1))
      = (∑ i ∈ Finset.range 99, stT74 (i+1)) + stT74 100 := by
    have h := Finset.sum_range_succ (fun i => stT74 (i+1)) 99
    simpa using h
  have hprev := st74_p99
  have hstep := st74_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 74`.** -/
theorem station_74_sign : hardyG (((74:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 74 100 (by norm_num) (by norm_num)
    ((56183/125000 : ℚ) : ℝ)
  have hchain := st74_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT74 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((74:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((56183/125000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((74:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((74:ℕ)):ℝ)+1) * ((((74:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((197509/296000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((921584212637/250000000000 : ℚ) : ℝ) - ((197509/296000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((56183/125000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((74:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((56183/125000 : ℚ) : ℝ)
        * (riemannZeta (line (((74:ℕ)):ℝ))).re
      - Real.sin ((56183/125000 : ℚ) : ℝ)
        * (riemannZeta (line (((74:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((74:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((74:ℕ)):ℝ)
      = ((((74:ℕ)):ℝ) * (Real.log (((74:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((74:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_74
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
  have hθwin : |(((56183/125000 : ℚ) : ℝ) + ((9:ℤ)) * (2*Real.pi) - Real.pi) - theta (((74:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((74:ℕ)):ℝ))
    (φ := ((56183/125000 : ℚ) : ℝ) + ((9:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((56183/125000 : ℚ) : ℝ) + ((9:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((56183/125000 : ℚ)) : ℝ) - Real.pi) + ((9:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((56183/125000 : ℚ)) : ℝ) - Real.pi) 9).1,
    (cos_sin_shift ((((56183/125000 : ℚ)) : ℝ) - Real.pi) 9).2]
  exact cos_sin_flip ((56183/125000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_74_sign
end AxiomAudit
