import RequestProject.DVPSqrtTable

/-!
# Station `t = 52` of the Hardy ladder (sign -)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT52 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((52 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((280901/1000000 : ℚ) : ℝ))

theorem st52_c1 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((480403/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -175563/2500000) (δ := 21/100000000) (ψ := 280901/1000000) 52 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t1 : ((240189/250000 : ℚ) : ℝ) ≤ stT52 1 := by
  have hc : ((240189/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((240189/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((240189/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c2 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-14299/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4840899/10000000) (δ := 203/50000000) (ψ := 280901/1000000) 52 6
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t2 : ((-25280835867/100000000000 : ℚ) : ℝ) ≤ stT52 2 := by
  have hc : ((-14301/40000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25280835867/100000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-14301/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c3 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((477923/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 186419/2500000) (δ := 239/50000000) (ψ := 280901/1000000) 52 9
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t3 : ((689786264699/1250000000000 : ℚ) : ℝ) ≤ stT52 3 := by
  have hc : ((238949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((689786264699/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((238949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c4 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-900349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3364209/5000000) (δ := 299/100000000) (ψ := 280901/1000000) 52 11
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t4 : ((-4501995900399/10000000000000 : ℚ) : ℝ) ≤ stT52 4 := by
  have hc : ((-900399/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4501995900399/10000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-900399/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c5 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-157013/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2160577/5000000) (δ := 221/50000000) (ψ := 280901/1000000) 52 13
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t5 : ((-87800887071/1250000000000 : ℚ) : ℝ) ≤ stT52 5 := by
  have hc : ((-157063/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87800887071/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-157063/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c6 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((211987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3392971/10000000) (δ := 171/50000000) (ψ := 280901/1000000) 52 15
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t6 : ((432614493817/5000000000000 : ℚ) : ℝ) ≤ stT52 6 := by
  have hc : ((211937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((432614493817/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((211937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c7 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((465169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187731/2000000) (δ := 273/100000000) (ψ := 280901/1000000) 52 16
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t7 : ((54939960273/156250000000 : ℚ) : ℝ) ≤ stT52 7 := by
  have hc : ((58143/62500 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54939960273/156250000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((58143/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c8 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((31859/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 647443/2500000) (δ := 319/100000000) (ψ := 280901/1000000) 52 17
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t8 : ((901019978451/5000000000000 : ℚ) : ℝ) ≤ stT52 8 := by
  have hc : ((254847/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((901019978451/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((254847/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c9 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((639121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 548401/2500000) (δ := 207/50000000) (ψ := 280901/1000000) 52 18
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t9 : ((2130236453643/10000000000000 : ℚ) : ℝ) ≤ stT52 9 := by
  have hc : ((639071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2130236453643/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((639071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c10 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((124667/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 182507/10000000) (δ := 93/20000000) (ψ := 280901/1000000) 52 19
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t10 : ((1576847290111/5000000000000 : ℚ) : ℝ) ≤ stT52 10 := by
  have hc : ((498643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1576847290111/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((498643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c11 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((155737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -783783/2500000) (δ := 99/25000000) (ψ := 280901/1000000) 52 20
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t11 : ((7335769929/78125000000 : ℚ) : ℝ) ≤ stT52 11 := by
  have hc : ((4866/15625 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7335769929/78125000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((4866/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c12 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-495849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7531617/10000000) (δ := 69/25000000) (ψ := 280901/1000000) 52 21
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t12 : ((-22366644707/78125000000 : ℚ) : ℝ) ≤ stT52 12 := by
  have hc : ((-247937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22366644707/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-247937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c13 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((102219/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 574787/2000000) (δ := 287/100000000) (ψ := 280901/1000000) 52 21
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t13 : ((1133878911/10000000000 : ℚ) : ℝ) ≤ stT52 13 := by
  have hc : ((204413/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1133878911/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((204413/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c14 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((143359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -399999/1250000) (δ := 193/50000000) (ψ := 280901/1000000) 52 22
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t14 : ((47884521051/625000000000 : ℚ) : ℝ) ≤ stT52 14 := by
  have hc : ((71667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47884521051/625000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((71667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c15 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-167987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2884541/5000000) (δ := 253/50000000) (ψ := 280901/1000000) 52 22
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t15 : ((-867545722011/5000000000000 : ℚ) : ℝ) ≤ stT52 15 := by
  have hc : ((-335999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-867545722011/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-335999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c16 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((40707/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -774437/5000000) (δ := 83/20000000) (ψ := 280901/1000000) 52 23
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t16 : ((81409/400000 : ℚ) : ℝ) ≤ stT52 16 := by
  have hc : ((81409/100000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81409/400000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((81409/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c17 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-410207/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6332327/10000000) (δ := 59/20000000) (ψ := 280901/1000000) 52 23
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t17 : ((-124369881603/625000000000 : ℚ) : ℝ) ≤ stT52 17 := by
  have hc : ((-51279/62500 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124369881603/625000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-51279/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c18 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((712307/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -972521/5000000) (δ := 319/100000000) (ψ := 280901/1000000) 52 24
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t18 : ((839402709327/5000000000000 : ℚ) : ℝ) ≤ stT52 18 := by
  have hc : ((712257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((839402709327/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((712257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c19 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-8927/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 317731/625000) (δ := 399/100000000) (ψ := 280901/1000000) 52 24
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t19 : ((-320035041/3125000000 : ℚ) : ℝ) ≤ stT52 19 := by
  have hc : ((-279/625 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320035041/3125000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-279/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c20 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-11659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3956139/10000000) (δ := 369/100000000) (ψ := 280901/1000000) 52 25
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t20 : ((-6545530053/2500000000000 : ℚ) : ℝ) ≤ stT52 20 := by
  have hc : ((-11709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6545530053/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-11709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c21 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((144477/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2386583/10000000) (δ := 157/50000000) (ψ := 280901/1000000) 52 25
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t21 : ((315247253681/2500000000000 : ℚ) : ℝ) ≤ stT52 21 := by
  have hc : ((288929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((315247253681/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((288929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c22 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-97319/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7273779/10000000) (δ := 263/100000000) (ψ := 280901/1000000) 52 26
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t22 : ((-6484235831/31250000000 : ℚ) : ℝ) ≤ stT52 22 := by
  have hc : ((-24331/25000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6484235831/31250000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-24331/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c23 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((206613/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1495049/10000000) (δ := 423/100000000) (ψ := 280901/1000000) 52 26
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t23 : ((107697948243/625000000000 : ℚ) : ℝ) ≤ stT52 23 := by
  have hc : ((413201/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107697948243/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((413201/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c24 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-44269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 40377/100000) (δ := 383/100000000) (ψ := 280901/1000000) 52 26
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t24 : ((-45232902099/5000000000000 : ℚ) : ℝ) ≤ stT52 24 := by
  have hc : ((-44319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45232902099/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-44319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c25 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-413729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1590851/2500000) (δ := 103/25000000) (ψ := 280901/1000000) 52 27
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t25 : ((-413754206877/2500000000000 : ℚ) : ℝ) ≤ stT52 25 := by
  have hc : ((-206877/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-413754206877/2500000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-206877/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c26 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((437373/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1264711/10000000) (δ := 83/25000000) (ψ := 280901/1000000) 52 27
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t26 : ((214427460257/1250000000000 : ℚ) : ℝ) ≤ stT52 26 := by
  have hc : ((109337/125000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((214427460257/1250000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((109337/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c27 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((7121/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 910383/2500000) (δ := 351/100000000) (ψ := 280901/1000000) 52 27
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t27 : ((219173607/10000000000 : ℚ) : ℝ) ≤ stT52 27 := by
  have hc : ((56943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219173607/10000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((56943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c28 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-978829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3669319/5000000) (δ := 481/100000000) (ψ := 280901/1000000) 52 28
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t28 : ((-1849908048417/10000000000000 : ℚ) : ℝ) ≤ stT52 28 := by
  have hc : ((-978879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1849908048417/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-978879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c29 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((444029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1388383/5000000) (δ := 361/100000000) (ψ := 280901/1000000) 52 28
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t29 : ((824448135987/10000000000000 : ℚ) : ℝ) ≤ stT52 29 := by
  have hc : ((443979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((824448135987/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((443979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c30 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((397383/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 407609/2500000) (δ := 221/50000000) (ψ := 280901/1000000) 52 28
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t30 : ((362736396139/2500000000000 : ℚ) : ℝ) ≤ stT52 30 := by
  have hc : ((198679/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((362736396139/2500000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((198679/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c31 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-707849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5893113/10000000) (δ := 481/100000000) (ψ := 280901/1000000) 52 28
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t31 : ((-635712415273/5000000000000 : ℚ) : ℝ) ≤ stT52 31 := by
  have hc : ((-707899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-635712415273/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-707899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c32 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-647433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35547/62500) (δ := 511/100000000) (ψ := 280901/1000000) 52 29
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t32 : ((-1144599080461/10000000000000 : ℚ) : ℝ) ≤ stT52 32 := by
  have hc : ((-647483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1144599080461/10000000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-647483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c33 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((780781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -421801/2500000) (δ := 83/25000000) (ψ := 280901/1000000) 52 29
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t33 : ((169884723407/1250000000000 : ℚ) : ℝ) ≤ stT52 33 := by
  have hc : ((780731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169884723407/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((780731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c34 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((639097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2193681/10000000) (δ := 391/100000000) (ψ := 280901/1000000) 52 29
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t34 : ((219191203859/2000000000000 : ℚ) : ℝ) ≤ stT52 34 := by
  have hc : ((639047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219191203859/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((639047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c35 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-727059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5962061/10000000) (δ := 83/25000000) (ψ := 280901/1000000) 52 29
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t35 : ((-1229038886681/10000000000000 : ℚ) : ℝ) ≤ stT52 35 := by
  have hc : ((-727109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1229038886681/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-727109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c36 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-189897/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6083689/10000000) (δ := 17/5000000) (ψ := 280901/1000000) 52 30
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t36 : ((-633031793273/5000000000000 : ℚ) : ℝ) ≤ stT52 36 := by
  have hc : ((-379819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-633031793273/5000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-379819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c37 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((532937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1260911/5000000) (δ := 23/5000000) (ψ := 280901/1000000) 52 30
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t37 : ((876060366243/10000000000000 : ℚ) : ℝ) ≤ stT52 37 := by
  have hc : ((532887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((876060366243/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((532887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c38 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((929397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 18901/200000) (δ := 303/100000000) (ψ := 280901/1000000) 52 30
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t38 : ((753799857129/5000000000000 : ℚ) : ℝ) ≤ stT52 38 := by
  have hc : ((929347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((753799857129/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((929347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c39 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-157293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4321863/10000000) (δ := 3/1000000) (ψ := 280901/1000000) 52 30
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t39 : ((-125975256863/5000000000000 : ℚ) : ℝ) ≤ stT52 39 := by
  have hc : ((-157343/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125975256863/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-157343/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c40 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-199073/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3806589/5000000) (δ := 263/100000000) (ψ := 280901/1000000) 52 30
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t40 : ((-314777895537/2000000000000 : ℚ) : ℝ) ≤ stT52 40 := by
  have hc : ((-199083/200000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-314777895537/2000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-199083/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c41 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-373799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -976949/2000000) (δ := 177/50000000) (ψ := 280901/1000000) 52 31
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t41 : ((-291927094781/5000000000000 : ℚ) : ℝ) ≤ stT52 41 := by
  have hc : ((-373849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291927094781/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-373849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c42 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((76431/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1752063/10000000) (δ := 409/100000000) (ψ := 280901/1000000) 52 31
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t42 : ((58963920029/500000000000 : ℚ) : ℝ) ≤ stT52 42 := by
  have hc : ((38213/50000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58963920029/500000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((38213/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c43 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((216611/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1306901/10000000) (δ := 449/100000000) (ψ := 280901/1000000) 52 31
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t43 : ((132123785409/1000000000000 : ℚ) : ℝ) ≤ stT52 43 := by
  have hc : ((433197/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((132123785409/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((433197/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c44 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-73443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4295539/10000000) (δ := 329/100000000) (ψ := 280901/1000000) 52 31
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t44 : ((-27689299419/1250000000000 : ℚ) : ℝ) ≤ stT52 44 := by
  have hc : ((-18367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27689299419/1250000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-18367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c45 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-967717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 721701/1000000) (δ := 237/50000000) (ψ := 280901/1000000) 52 31
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t45 : ((-180332735013/1250000000000 : ℚ) : ℝ) ≤ stT52 45 := by
  have hc : ((-967767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-180332735013/1250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-967767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c46 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-157719/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -176053/312500) (δ := 121/25000000) (ψ := 280901/1000000) 52 32
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t46 : ((-23256247823/250000000000 : ℚ) : ℝ) ≤ stT52 46 := by
  have hc : ((-315463/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).2
  have h0 : (0:ℝ) ≤ ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23256247823/250000000000 : ℚ) : ℝ)
      = ((73721/500000 : ℚ) : ℝ) * ((-315463/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c47 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((421991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2837889/10000000) (δ := 519/100000000) (ψ := 280901/1000000) 52 32
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t47 : ((615463817709/10000000000000 : ℚ) : ℝ) ≤ stT52 47 := by
  have hc : ((421941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((615463817709/10000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((421941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c48 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((199837/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50473/5000000) (δ := 479/100000000) (ψ := 280901/1000000) 52 32
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t48 : ((2307402369/16000000000 : ℚ) : ℝ) ≤ stT52 48 := by
  have hc : ((199827/200000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2307402369/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((199827/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c49 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((256627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1289781/5000000) (δ := 131/25000000) (ψ := 280901/1000000) 52 32
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t49 : ((183287087871/2500000000000 : ℚ) : ℝ) ≤ stT52 49 := by
  have hc : ((128301/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((183287087871/2500000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((128301/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c50 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-244773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2602957/5000000) (δ := 479/100000000) (ψ := 280901/1000000) 52 32
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t50 : ((-86549189693/1250000000000 : ℚ) : ℝ) ≤ stT52 50 := by
  have hc : ((-122399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86549189693/1250000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-122399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c51 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-199913/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1556051/2000000) (δ := 359/100000000) (ψ := 280901/1000000) 52 32
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t51 : ((-279948378363/2000000000000 : ℚ) : ℝ) ≤ stT52 51 := by
  have hc : ((-199923/200000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279948378363/2000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-199923/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c52 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-111363/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5403357/10000000) (δ := 107/25000000) (ψ := 280901/1000000) 52 33
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t52 : ((-154446619123/2000000000000 : ℚ) : ℝ) ≤ stT52 52 := by
  have hc : ((-111373/200000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154446619123/2000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-111373/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c53 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((389381/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -731773/2500000) (δ := 117/25000000) (ψ := 280901/1000000) 52 33
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t53 : ((106957401651/2000000000000 : ℚ) : ℝ) ≤ stT52 53 := by
  have hc : ((389331/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((106957401651/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((389331/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c54 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((196059/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -248557/5000000) (δ := 67/25000000) (ψ := 280901/1000000) 52 33
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t54 : ((266788772523/2000000000000 : ℚ) : ℝ) ≤ stT52 54 := by
  have hc : ((196049/200000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((266788772523/2000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((196049/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c55 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((728059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 944137/5000000) (δ := 91/20000000) (ψ := 280901/1000000) 52 33
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t55 : ((981646607591/10000000000000 : ℚ) : ℝ) ≤ stT52 55 := by
  have hc : ((728009/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((981646607591/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((728009/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c56 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-121177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4230679/10000000) (δ := 91/20000000) (ψ := 280901/1000000) 52 33
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t56 : ((-161996488689/10000000000000 : ℚ) : ℝ) ≤ stT52 56 := by
  have hc : ((-121227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-161996488689/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-121227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c57 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-863341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 816453/1250000) (δ := 67/20000000) (ψ := 280901/1000000) 52 33
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t57 : ((-1143589871403/10000000000000 : ℚ) : ℝ) ≤ stT52 57 := by
  have hc : ((-863391/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1143589871403/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-863391/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c58 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-930351/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1728853/2500000) (δ := 457/100000000) (ψ := 280901/1000000) 52 34
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t58 : ((-244335397813/2000000000000 : ℚ) : ℝ) ≤ stT52 58 := by
  have hc : ((-930401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-244335397813/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-930401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c59 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-75421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293321/625000) (δ := 297/100000000) (ψ := 280901/1000000) 52 34
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t59 : ((-19641223863/500000000000 : ℚ) : ℝ) ≤ stT52 59 := by
  have hc : ((-150867/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19641223863/500000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-150867/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c60 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((8399/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2508211/10000000) (δ := 153/50000000) (ψ := 280901/1000000) 52 34
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t60 : ((173472800271/2500000000000 : ℚ) : ℝ) ≤ stT52 60 := by
  have hc : ((268743/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((173472800271/2500000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((268743/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c61 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((247421/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -359401/10000000) (δ := 173/50000000) (ψ := 280901/1000000) 52 34
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t61 : ((39596740791/312500000000 : ℚ) : ℝ) ≤ stT52 61 := by
  have hc : ((494817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39596740791/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((494817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c62 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((76369/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 877233/5000000) (δ := 213/50000000) (ψ := 280901/1000000) 52 34
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t62 : ((24245589091/250000000000 : ℚ) : ℝ) ≤ stT52 62 := by
  have hc : ((19091/25000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24245589091/250000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((19091/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c63 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((36983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3834511/10000000) (δ := 377/100000000) (ψ := 280901/1000000) 52 34
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t63 : ((46531184973/10000000000000 : ℚ) : ℝ) ≤ stT52 63 := by
  have hc : ((36933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46531184973/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((36933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c64 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-140929/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5881797/10000000) (δ := 213/50000000) (ψ := 280901/1000000) 52 34
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t64 : ((-176173890939/2000000000000 : ℚ) : ℝ) ≤ stT52 64 := by
  have hc : ((-140939/200000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-176173890939/2000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-140939/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c65 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-19997/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3905311/5000000) (δ := 357/100000000) (ψ := 280901/1000000) 52 35
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t65 : ((-3100559913/25000000000 : ℚ) : ℝ) ≤ stT52 65 := by
  have hc : ((-9999/10000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3100559913/25000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-9999/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c66 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-688591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116517/200000) (δ := 143/50000000) (ψ := 280901/1000000) 52 35
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t66 : ((-169531707303/2000000000000 : ℚ) : ℝ) ≤ stT52 66 := by
  have hc : ((-688641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-169531707303/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-688641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c67 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((2803/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1935463/5000000) (δ := 203/50000000) (ψ := 280901/1000000) 52 35
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t67 : ((6833545389/2500000000000 : ℚ) : ℝ) ≤ stT52 67 := by
  have hc : ((11187/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6833545389/2500000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((11187/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c68 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((712329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -388993/2000000) (δ := 243/50000000) (ψ := 280901/1000000) 52 35
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t68 : ((431882536581/5000000000000 : ℚ) : ℝ) ≤ stT52 68 := by
  have hc : ((712279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((431882536581/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((712279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c69 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((499911/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -47121/10000000) (δ := 243/50000000) (ψ := 280901/1000000) 52 35
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t69 : ((150447940047/1250000000000 : ℚ) : ℝ) ≤ stT52 69 := by
  have hc : ((249943/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((150447940047/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((249943/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c70 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((745597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 364683/2000000) (δ := 143/50000000) (ψ := 280901/1000000) 52 35
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t70 : ((222774662429/2500000000000 : ℚ) : ℝ) ≤ stT52 70 := by
  have hc : ((745547/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222774662429/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((745547/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c71 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((103643/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3667417/10000000) (δ := 397/100000000) (ψ := 280901/1000000) 52 35
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t71 : ((122942204133/10000000000000 : ℚ) : ℝ) ≤ stT52 71 := by
  have hc : ((103593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((122942204133/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((103593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c72 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-145961/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5485629/10000000) (δ := 203/50000000) (ψ := 280901/1000000) 52 35
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t72 : ((-21503940179/312500000000 : ℚ) : ℝ) ≤ stT52 72 := by
  have hc : ((-291947/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21503940179/312500000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-291947/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c73 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-486823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 181969/250000) (δ := 163/50000000) (ψ := 280901/1000000) 52 35
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t73 : ((-2225831021/19531250000 : ℚ) : ℝ) ≤ stT52 73 := by
  have hc : ((-15214/15625 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2225831021/19531250000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-15214/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c74 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-88819/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1665117/2500000) (δ := 487/100000000) (ψ := 280901/1000000) 52 36
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t74 : ((-12906982131/125000000000 : ℚ) : ℝ) ≤ stT52 74 := by
  have hc : ((-11103/12500 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12906982131/125000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-11103/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c75 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-96293/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196619/400000) (δ := 109/25000000) (ψ := 280901/1000000) 52 36
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t75 : ((-222408114311/5000000000000 : ℚ) : ℝ) ≤ stT52 75 := by
  have hc : ((-192611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-222408114311/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-192611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c76 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((18073/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -798399/2500000) (δ := 79/25000000) (ψ := 280901/1000000) 52 36
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t76 : ((82910224301/2500000000000 : ℚ) : ℝ) ≤ stT52 76 := by
  have hc : ((144559/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((82910224301/2500000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((144559/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c77 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((413319/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59769/400000) (δ := 99/25000000) (ψ := 280901/1000000) 52 36
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t77 : ((47099190887/500000000000 : ℚ) : ℝ) ≤ stT52 77 := by
  have hc : ((206647/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47099190887/500000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((206647/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c78 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((249329/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 183217/10000000) (δ := 99/25000000) (ψ := 280901/1000000) 52 36
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t78 : ((564590677341/5000000000000 : ℚ) : ℝ) ≤ stT52 78 := by
  have hc : ((498633/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((564590677341/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((498633/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c79 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((14827/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1839291/10000000) (δ := 287/100000000) (ψ := 280901/1000000) 52 36
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t79 : ((8340269931/100000000000 : ℚ) : ℝ) ≤ stT52 79 := by
  have hc : ((7413/10000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8340269931/100000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((7413/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c80 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((179997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 868633/2500000) (δ := 89/25000000) (ψ := 280901/1000000) 52 36
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t80 : ((201186684251/10000000000000 : ℚ) : ℝ) ≤ stT52 80 := by
  have hc : ((179947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((201186684251/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((179947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c81 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-112103/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 254473/500000) (δ := 287/100000000) (ψ := 280901/1000000) 52 36
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t81 : ((-31143219359/625000000000 : ℚ) : ℝ) ≤ stT52 81 := by
  have hc : ((-224231/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31143219359/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-224231/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c82 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-892579/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1671143/2500000) (δ := 69/25000000) (ψ := 280901/1000000) 52 36
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t82 : ((-246436121691/2500000000000 : ℚ) : ℝ) ≤ stT52 82 := by
  have hc : ((-892629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246436121691/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-892629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c83 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-493409/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3723807/5000000) (δ := 93/20000000) (ψ := 280901/1000000) 52 37
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t83 : ((-270807188031/2500000000000 : ℚ) : ℝ) ≤ stT52 83 := by
  have hc : ((-246717/250000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270807188031/2500000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-246717/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c84 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-70717/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -589071/1000000) (δ := 109/20000000) (ψ := 280901/1000000) 52 37
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t84 : ((-3858203349/50000000000 : ℚ) : ℝ) ≤ stT52 84 := by
  have hc : ((-35361/50000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3858203349/50000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-35361/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c85 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-169277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -435223/1000000) (δ := 149/50000000) (ψ := 280901/1000000) 52 37
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t85 : ((-183661038531/10000000000000 : ℚ) : ℝ) ≤ stT52 85 := by
  have hc : ((-169327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-183661038531/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-169327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c86 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((212109/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -566349/2000000) (δ := 249/50000000) (ψ := 280901/1000000) 52 37
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t86 : ((57173975867/1250000000000 : ℚ) : ℝ) ≤ stT52 86 := by
  have hc : ((53021/125000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57173975867/1250000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((53021/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c87 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((86203/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -664419/5000000) (δ := 17/4000000) (ψ := 280901/1000000) 52 37
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t87 : ((2887934693/31250000000 : ℚ) : ℝ) ≤ stT52 87 := by
  have hc : ((43099/50000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2887934693/31250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((43099/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c88 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((998031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 39223/2500000) (δ := 93/20000000) (ψ := 280901/1000000) 52 37
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t88 : ((1063850739943/10000000000000 : ℚ) : ℝ) ≤ stT52 88 := by
  have hc : ((997981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1063850739943/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((997981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c89 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((397941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 325167/2000000) (δ := 189/50000000) (ψ := 280901/1000000) 52 37
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t89 : ((105447441563/1250000000000 : ℚ) : ℝ) ≤ stT52 89 := by
  have hc : ((99479/125000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105447441563/1250000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((99479/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c90 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((332969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 769591/2500000) (δ := 189/50000000) (ψ := 280901/1000000) 52 37
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t90 : ((87731813637/2500000000000 : ℚ) : ℝ) ≤ stT52 90 := by
  have hc : ((332919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87731813637/2500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((332919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c91 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-11649/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2257421/5000000) (δ := 269/50000000) (ψ := 280901/1000000) 52 37
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t91 : ((-4885637071/200000000000 : ℚ) : ℝ) ≤ stT52 91 := by
  have hc : ((-23303/100000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4885637071/200000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-23303/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c92 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-719757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2967811/5000000) (δ := 209/50000000) (ψ := 280901/1000000) 52 37
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t92 : ((-750451343411/10000000000000 : ℚ) : ℝ) ≤ stT52 92 := by
  have hc : ((-719807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-750451343411/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-719807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c93 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-39161/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7341041/10000000) (δ := 249/50000000) (ψ := 280901/1000000) 52 37
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t93 : ((-5076268897/50000000000 : ℚ) : ℝ) ≤ stT52 93 := by
  have hc : ((-39163/40000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).2
  have h0 : (0:ℝ) ≤ ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5076268897/50000000000 : ℚ) : ℝ)
      = ((129619/1250000 : ℚ) : ℝ) * ((-39163/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c94 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-939037/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1395307/2000000) (δ := 429/100000000) (ψ := 280901/1000000) 52 38
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t94 : ((-484297495857/5000000000000 : ℚ) : ℝ) ≤ stT52 94 := by
  have hc : ((-939087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-484297495857/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-939087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c95 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-77579/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5600861/10000000) (δ := 469/100000000) (ψ := 280901/1000000) 52 38
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t95 : ((-318403348839/5000000000000 : ℚ) : ℝ) ≤ stT52 95 := by
  have hc : ((-310341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-318403348839/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-310341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c96 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((-24943/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529949/1250000) (δ := 469/100000000) (ψ := 280901/1000000) 52 38
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t96 : ((-25467555813/2000000000000 : ℚ) : ℝ) ≤ stT52 96 := by
  have hc : ((-24953/200000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25467555813/2000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-24953/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c97 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((201057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2892429/10000000) (δ := 429/100000000) (ψ := 280901/1000000) 52 38
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t97 : ((12757314817/312500000000 : ℚ) : ℝ) ≤ stT52 97 := by
  have hc : ((25129/62500 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12757314817/312500000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((25129/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c98 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((405881/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -389771/2500000) (δ := 429/100000000) (ψ := 280901/1000000) 52 38
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t98 : ((1601469727/19531250000 : ℚ) : ℝ) ≤ stT52 98 := by
  have hc : ((12683/15625 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1601469727/19531250000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((12683/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c99 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((995423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -59819/2500000) (δ := 269/100000000) (ψ := 280901/1000000) 52 38
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t99 : ((1000386693801/10000000000000 : ℚ) : ℝ) ≤ stT52 99 := by
  have hc : ((995373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1000386693801/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((995373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_c100 :
    |Real.cos (((52 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((280901/1000000 : ℚ) : ℝ))
      - ((910251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1067267/10000000) (δ := 429/100000000) (ψ := 280901/1000000) 52 38
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st52_t100 : ((910200089799/10000000000000 : ℚ) : ℝ) ≤ stT52 100 := by
  have hc : ((910201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((52 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((280901/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st52_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((910200089799/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((910201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st52_p1 : ((240189/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT52 (i+1) := by
  rw [Finset.sum_range_one]
  exact st52_t1

theorem st52_p2 : ((70794764133/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT52 (i+1))
      = (∑ i ∈ Finset.range 1, stT52 (i+1)) + stT52 2 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 1
    simpa using h
  have hprev := st52_p1
  have hstep := st52_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p3 : ((3149441632723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT52 (i+1))
      = (∑ i ∈ Finset.range 2, stT52 (i+1)) + stT52 3 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 2
    simpa using h
  have hprev := st52_p2
  have hstep := st52_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p4 : ((8095770630493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT52 (i+1))
      = (∑ i ∈ Finset.range 3, stT52 (i+1)) + stT52 4 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 3
    simpa using h
  have hprev := st52_p3
  have hstep := st52_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p5 : ((295734541357/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT52 (i+1))
      = (∑ i ∈ Finset.range 4, stT52 (i+1)) + stT52 5 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 4
    simpa using h
  have hprev := st52_p4
  have hstep := st52_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p6 : ((8258592521559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT52 (i+1))
      = (∑ i ∈ Finset.range 5, stT52 (i+1)) + stT52 6 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 5
    simpa using h
  have hprev := st52_p5
  have hstep := st52_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p7 : ((11774749979031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT52 (i+1))
      = (∑ i ∈ Finset.range 6, stT52 (i+1)) + stT52 7 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 6
    simpa using h
  have hprev := st52_p6
  have hstep := st52_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p8 : ((13576789935933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT52 (i+1))
      = (∑ i ∈ Finset.range 7, stT52 (i+1)) + stT52 8 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 7
    simpa using h
  have hprev := st52_p7
  have hstep := st52_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p9 : ((1963378298697/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT52 (i+1))
      = (∑ i ∈ Finset.range 8, stT52 (i+1)) + stT52 9 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 8
    simpa using h
  have hprev := st52_p8
  have hstep := st52_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p10 : ((9430360484899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT52 (i+1))
      = (∑ i ∈ Finset.range 9, stT52 (i+1)) + stT52 10 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 9
    simpa using h
  have hprev := st52_p9
  have hstep := st52_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p11 : ((1979969952071/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT52 (i+1))
      = (∑ i ∈ Finset.range 10, stT52 (i+1)) + stT52 11 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 10
    simpa using h
  have hprev := st52_p10
  have hstep := st52_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p12 : ((8468384499107/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT52 (i+1))
      = (∑ i ∈ Finset.range 11, stT52 (i+1)) + stT52 12 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 11
    simpa using h
  have hprev := st52_p11
  have hstep := st52_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p13 : ((9035323954607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT52 (i+1))
      = (∑ i ∈ Finset.range 12, stT52 (i+1)) + stT52 13 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 12
    simpa using h
  have hprev := st52_p12
  have hstep := st52_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p14 : ((1883680024603/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT52 (i+1))
      = (∑ i ∈ Finset.range 13, stT52 (i+1)) + stT52 14 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 13
    simpa using h
  have hprev := st52_p13
  have hstep := st52_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p15 : ((2137713600251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT52 (i+1))
      = (∑ i ∈ Finset.range 14, stT52 (i+1)) + stT52 15 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 14
    simpa using h
  have hprev := st52_p14
  have hstep := st52_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p16 : ((2392116725251/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT52 (i+1))
      = (∑ i ∈ Finset.range 15, stT52 (i+1)) + stT52 16 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 15
    simpa using h
  have hprev := st52_p15
  have hstep := st52_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p17 : ((428675392409/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT52 (i+1))
      = (∑ i ∈ Finset.range 16, stT52 (i+1)) + stT52 17 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 16
    simpa using h
  have hprev := st52_p16
  have hstep := st52_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p18 : ((9412910557507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT52 (i+1))
      = (∑ i ∈ Finset.range 17, stT52 (i+1)) + stT52 18 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 17
    simpa using h
  have hprev := st52_p17
  have hstep := st52_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p19 : ((8900854491907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT52 (i+1))
      = (∑ i ∈ Finset.range 18, stT52 (i+1)) + stT52 19 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 18
    simpa using h
  have hprev := st52_p18
  have hstep := st52_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p20 : ((8887763431801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT52 (i+1))
      = (∑ i ∈ Finset.range 19, stT52 (i+1)) + stT52 20 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 19
    simpa using h
  have hprev := st52_p19
  have hstep := st52_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p21 : ((9518257939163/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT52 (i+1))
      = (∑ i ∈ Finset.range 20, stT52 (i+1)) + stT52 21 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 20
    simpa using h
  have hprev := st52_p20
  have hstep := st52_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p22 : ((8480780206203/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT52 (i+1))
      = (∑ i ∈ Finset.range 21, stT52 (i+1)) + stT52 22 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 21
    simpa using h
  have hprev := st52_p21
  have hstep := st52_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p23 : ((9342363792147/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT52 (i+1))
      = (∑ i ∈ Finset.range 22, stT52 (i+1)) + stT52 23 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 22
    simpa using h
  have hprev := st52_p22
  have hstep := st52_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p24 : ((145267670157/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT52 (i+1))
      = (∑ i ∈ Finset.range 23, stT52 (i+1)) + stT52 24 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 23
    simpa using h
  have hprev := st52_p23
  have hstep := st52_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p25 : ((4234811238147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT52 (i+1))
      = (∑ i ∈ Finset.range 24, stT52 (i+1)) + stT52 25 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 24
    simpa using h
  have hprev := st52_p24
  have hstep := st52_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p26 : ((4663666158661/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT52 (i+1))
      = (∑ i ∈ Finset.range 25, stT52 (i+1)) + stT52 26 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 25
    simpa using h
  have hprev := st52_p25
  have hstep := st52_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p27 : ((4718459560411/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT52 (i+1))
      = (∑ i ∈ Finset.range 26, stT52 (i+1)) + stT52 27 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 26
    simpa using h
  have hprev := st52_p26
  have hstep := st52_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p28 : ((17023930193227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT52 (i+1))
      = (∑ i ∈ Finset.range 27, stT52 (i+1)) + stT52 28 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 27
    simpa using h
  have hprev := st52_p27
  have hstep := st52_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p29 : ((8924189164607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT52 (i+1))
      = (∑ i ∈ Finset.range 28, stT52 (i+1)) + stT52 29 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 28
    simpa using h
  have hprev := st52_p28
  have hstep := st52_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p30 : ((1929932391377/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT52 (i+1))
      = (∑ i ∈ Finset.range 29, stT52 (i+1)) + stT52 30 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 29
    simpa using h
  have hprev := st52_p29
  have hstep := st52_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p31 : ((2253487385403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT52 (i+1))
      = (∑ i ∈ Finset.range 30, stT52 (i+1)) + stT52 31 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 30
    simpa using h
  have hprev := st52_p30
  have hstep := st52_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p32 : ((16883300002763/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT52 (i+1))
      = (∑ i ∈ Finset.range 31, stT52 (i+1)) + stT52 32 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 31
    simpa using h
  have hprev := st52_p31
  have hstep := st52_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p33 : ((18242377790019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT52 (i+1))
      = (∑ i ∈ Finset.range 32, stT52 (i+1)) + stT52 33 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 32
    simpa using h
  have hprev := st52_p32
  have hstep := st52_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p34 : ((9669166904657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT52 (i+1))
      = (∑ i ∈ Finset.range 33, stT52 (i+1)) + stT52 34 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 33
    simpa using h
  have hprev := st52_p33
  have hstep := st52_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p35 : ((18109294922633/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT52 (i+1))
      = (∑ i ∈ Finset.range 34, stT52 (i+1)) + stT52 35 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 34
    simpa using h
  have hprev := st52_p34
  have hstep := st52_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p36 : ((16843231336087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT52 (i+1))
      = (∑ i ∈ Finset.range 35, stT52 (i+1)) + stT52 36 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 35
    simpa using h
  have hprev := st52_p35
  have hstep := st52_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p37 : ((1771929170233/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT52 (i+1))
      = (∑ i ∈ Finset.range 36, stT52 (i+1)) + stT52 37 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 36
    simpa using h
  have hprev := st52_p36
  have hstep := st52_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p38 : ((4806722854147/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT52 (i+1))
      = (∑ i ∈ Finset.range 37, stT52 (i+1)) + stT52 38 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 37
    simpa using h
  have hprev := st52_p37
  have hstep := st52_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p39 : ((9487470451431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT52 (i+1))
      = (∑ i ∈ Finset.range 38, stT52 (i+1)) + stT52 39 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 38
    simpa using h
  have hprev := st52_p38
  have hstep := st52_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p40 : ((17401051425177/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT52 (i+1))
      = (∑ i ∈ Finset.range 39, stT52 (i+1)) + stT52 40 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 39
    simpa using h
  have hprev := st52_p39
  have hstep := st52_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p41 : ((3363439447123/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT52 (i+1))
      = (∑ i ∈ Finset.range 40, stT52 (i+1)) + stT52 41 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 40
    simpa using h
  have hprev := st52_p40
  have hstep := st52_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p42 : ((3599295127239/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT52 (i+1))
      = (∑ i ∈ Finset.range 41, stT52 (i+1)) + stT52 42 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 41
    simpa using h
  have hprev := st52_p41
  have hstep := st52_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p43 : ((3863542698057/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT52 (i+1))
      = (∑ i ∈ Finset.range 42, stT52 (i+1)) + stT52 43 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 42
    simpa using h
  have hprev := st52_p42
  have hstep := st52_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p44 : ((19096199094933/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT52 (i+1))
      = (∑ i ∈ Finset.range 43, stT52 (i+1)) + stT52 44 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 43
    simpa using h
  have hprev := st52_p43
  have hstep := st52_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p45 : ((17653537214829/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT52 (i+1))
      = (∑ i ∈ Finset.range 44, stT52 (i+1)) + stT52 45 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 44
    simpa using h
  have hprev := st52_p44
  have hstep := st52_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p46 : ((16723287301909/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT52 (i+1))
      = (∑ i ∈ Finset.range 45, stT52 (i+1)) + stT52 46 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 45
    simpa using h
  have hprev := st52_p45
  have hstep := st52_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p47 : ((8669375559809/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT52 (i+1))
      = (∑ i ∈ Finset.range 46, stT52 (i+1)) + stT52 47 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 46
    simpa using h
  have hprev := st52_p46
  have hstep := st52_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p48 : ((18780877600243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT52 (i+1))
      = (∑ i ∈ Finset.range 47, stT52 (i+1)) + stT52 48 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 47
    simpa using h
  have hprev := st52_p47
  have hstep := st52_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p49 : ((19514025951727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT52 (i+1))
      = (∑ i ∈ Finset.range 48, stT52 (i+1)) + stT52 49 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 48
    simpa using h
  have hprev := st52_p48
  have hstep := st52_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p50 : ((18821632434183/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT52 (i+1))
      = (∑ i ∈ Finset.range 49, stT52 (i+1)) + stT52 50 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 49
    simpa using h
  have hprev := st52_p49
  have hstep := st52_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p51 : ((544434079449/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT52 (i+1))
      = (∑ i ∈ Finset.range 50, stT52 (i+1)) + stT52 51 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 50
    simpa using h
  have hprev := st52_p50
  have hstep := st52_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p52 : ((16649657446753/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT52 (i+1))
      = (∑ i ∈ Finset.range 51, stT52 (i+1)) + stT52 52 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 51
    simpa using h
  have hprev := st52_p51
  have hstep := st52_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p53 : ((537013889219/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT52 (i+1))
      = (∑ i ∈ Finset.range 52, stT52 (i+1)) + stT52 53 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 52
    simpa using h
  have hprev := st52_p52
  have hstep := st52_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p54 : ((18518388317623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT52 (i+1))
      = (∑ i ∈ Finset.range 53, stT52 (i+1)) + stT52 54 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 53
    simpa using h
  have hprev := st52_p53
  have hstep := st52_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p55 : ((9750017462607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT52 (i+1))
      = (∑ i ∈ Finset.range 54, stT52 (i+1)) + stT52 55 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 54
    simpa using h
  have hprev := st52_p54
  have hstep := st52_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p56 : ((773521537461/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT52 (i+1))
      = (∑ i ∈ Finset.range 55, stT52 (i+1)) + stT52 56 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 55
    simpa using h
  have hprev := st52_p55
  have hstep := st52_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p57 : ((9097224282561/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT52 (i+1))
      = (∑ i ∈ Finset.range 56, stT52 (i+1)) + stT52 57 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 56
    simpa using h
  have hprev := st52_p56
  have hstep := st52_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p58 : ((16972771576057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT52 (i+1))
      = (∑ i ∈ Finset.range 57, stT52 (i+1)) + stT52 58 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 57
    simpa using h
  have hprev := st52_p57
  have hstep := st52_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p59 : ((16579947098797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT52 (i+1))
      = (∑ i ∈ Finset.range 58, stT52 (i+1)) + stT52 59 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 58
    simpa using h
  have hprev := st52_p58
  have hstep := st52_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p60 : ((17273838299881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT52 (i+1))
      = (∑ i ∈ Finset.range 59, stT52 (i+1)) + stT52 60 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 59
    simpa using h
  have hprev := st52_p59
  have hstep := st52_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p61 : ((18540934005193/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT52 (i+1))
      = (∑ i ∈ Finset.range 60, stT52 (i+1)) + stT52 61 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 60
    simpa using h
  have hprev := st52_p60
  have hstep := st52_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p62 : ((19510757568833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT52 (i+1))
      = (∑ i ∈ Finset.range 61, stT52 (i+1)) + stT52 62 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 61
    simpa using h
  have hprev := st52_p61
  have hstep := st52_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p63 : ((9778644376903/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT52 (i+1))
      = (∑ i ∈ Finset.range 62, stT52 (i+1)) + stT52 63 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 62
    simpa using h
  have hprev := st52_p62
  have hstep := st52_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p64 : ((18676419299111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT52 (i+1))
      = (∑ i ∈ Finset.range 63, stT52 (i+1)) + stT52 64 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 63
    simpa using h
  have hprev := st52_p63
  have hstep := st52_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p65 : ((17436195333911/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT52 (i+1))
      = (∑ i ∈ Finset.range 64, stT52 (i+1)) + stT52 65 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 64
    simpa using h
  have hprev := st52_p64
  have hstep := st52_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p66 : ((4147134199349/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT52 (i+1))
      = (∑ i ∈ Finset.range 65, stT52 (i+1)) + stT52 66 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 65
    simpa using h
  have hprev := st52_p65
  have hstep := st52_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p67 : ((2076983872369/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT52 (i+1))
      = (∑ i ∈ Finset.range 66, stT52 (i+1)) + stT52 67 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 66
    simpa using h
  have hprev := st52_p66
  have hstep := st52_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p68 : ((8739818026057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT52 (i+1))
      = (∑ i ∈ Finset.range 67, stT52 (i+1)) + stT52 68 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 67
    simpa using h
  have hprev := st52_p67
  have hstep := st52_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p69 : ((1868321957249/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT52 (i+1))
      = (∑ i ∈ Finset.range 68, stT52 (i+1)) + stT52 69 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 68
    simpa using h
  have hprev := st52_p68
  have hstep := st52_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p70 : ((9787159111103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT52 (i+1))
      = (∑ i ∈ Finset.range 69, stT52 (i+1)) + stT52 70 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 69
    simpa using h
  have hprev := st52_p69
  have hstep := st52_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p71 : ((19697260426339/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT52 (i+1))
      = (∑ i ∈ Finset.range 70, stT52 (i+1)) + stT52 71 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 70
    simpa using h
  have hprev := st52_p70
  have hstep := st52_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p72 : ((19009134340611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT52 (i+1))
      = (∑ i ∈ Finset.range 71, stT52 (i+1)) + stT52 72 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 71
    simpa using h
  have hprev := st52_p71
  have hstep := st52_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p73 : ((17869508857859/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT52 (i+1))
      = (∑ i ∈ Finset.range 72, stT52 (i+1)) + stT52 73 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 72
    simpa using h
  have hprev := st52_p72
  have hstep := st52_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p74 : ((16836950287379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT52 (i+1))
      = (∑ i ∈ Finset.range 73, stT52 (i+1)) + stT52 74 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 73
    simpa using h
  have hprev := st52_p73
  have hstep := st52_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p75 : ((16392134058757/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT52 (i+1))
      = (∑ i ∈ Finset.range 74, stT52 (i+1)) + stT52 75 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 74
    simpa using h
  have hprev := st52_p74
  have hstep := st52_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p76 : ((16723774955961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT52 (i+1))
      = (∑ i ∈ Finset.range 75, stT52 (i+1)) + stT52 76 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 75
    simpa using h
  have hprev := st52_p75
  have hstep := st52_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p77 : ((17665758773701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT52 (i+1))
      = (∑ i ∈ Finset.range 76, stT52 (i+1)) + stT52 77 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 76
    simpa using h
  have hprev := st52_p76
  have hstep := st52_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p78 : ((18794940128383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT52 (i+1))
      = (∑ i ∈ Finset.range 77, stT52 (i+1)) + stT52 78 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 77
    simpa using h
  have hprev := st52_p77
  have hstep := st52_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p79 : ((19628967121483/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT52 (i+1))
      = (∑ i ∈ Finset.range 78, stT52 (i+1)) + stT52 79 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 78
    simpa using h
  have hprev := st52_p78
  have hstep := st52_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p80 : ((9915076902867/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT52 (i+1))
      = (∑ i ∈ Finset.range 79, stT52 (i+1)) + stT52 80 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 79
    simpa using h
  have hprev := st52_p79
  have hstep := st52_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p81 : ((1933186229599/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT52 (i+1))
      = (∑ i ∈ Finset.range 80, stT52 (i+1)) + stT52 81 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 80
    simpa using h
  have hprev := st52_p80
  have hstep := st52_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p82 : ((9173058904613/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT52 (i+1))
      = (∑ i ∈ Finset.range 81, stT52 (i+1)) + stT52 82 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 81
    simpa using h
  have hprev := st52_p81
  have hstep := st52_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p83 : ((8631444528551/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT52 (i+1))
      = (∑ i ∈ Finset.range 82, stT52 (i+1)) + stT52 83 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 82
    simpa using h
  have hprev := st52_p82
  have hstep := st52_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p84 : ((8245624193651/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT52 (i+1))
      = (∑ i ∈ Finset.range 83, stT52 (i+1)) + stT52 84 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 83
    simpa using h
  have hprev := st52_p83
  have hstep := st52_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p85 : ((16307587348771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT52 (i+1))
      = (∑ i ∈ Finset.range 84, stT52 (i+1)) + stT52 85 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 84
    simpa using h
  have hprev := st52_p84
  have hstep := st52_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p86 : ((16764979155707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT52 (i+1))
      = (∑ i ∈ Finset.range 85, stT52 (i+1)) + stT52 86 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 85
    simpa using h
  have hprev := st52_p85
  have hstep := st52_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p87 : ((17689118257467/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT52 (i+1))
      = (∑ i ∈ Finset.range 86, stT52 (i+1)) + stT52 87 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 86
    simpa using h
  have hprev := st52_p86
  have hstep := st52_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p88 : ((1875296899741/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT52 (i+1))
      = (∑ i ∈ Finset.range 87, stT52 (i+1)) + stT52 88 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 87
    simpa using h
  have hprev := st52_p87
  have hstep := st52_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p89 : ((9798274264957/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT52 (i+1))
      = (∑ i ∈ Finset.range 88, stT52 (i+1)) + stT52 89 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 88
    simpa using h
  have hprev := st52_p88
  have hstep := st52_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p90 : ((9973737892231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT52 (i+1))
      = (∑ i ∈ Finset.range 89, stT52 (i+1)) + stT52 90 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 89
    simpa using h
  have hprev := st52_p89
  have hstep := st52_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p91 : ((615724810341/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT52 (i+1))
      = (∑ i ∈ Finset.range 90, stT52 (i+1)) + stT52 91 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 90
    simpa using h
  have hprev := st52_p90
  have hstep := st52_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p92 : ((18952742587501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT52 (i+1))
      = (∑ i ∈ Finset.range 91, stT52 (i+1)) + stT52 92 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 91
    simpa using h
  have hprev := st52_p91
  have hstep := st52_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p93 : ((17937488808101/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT52 (i+1))
      = (∑ i ∈ Finset.range 92, stT52 (i+1)) + stT52 93 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 92
    simpa using h
  have hprev := st52_p92
  have hstep := st52_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p94 : ((16968893816387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT52 (i+1))
      = (∑ i ∈ Finset.range 93, stT52 (i+1)) + stT52 94 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 93
    simpa using h
  have hprev := st52_p93
  have hstep := st52_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p95 : ((16332087118709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT52 (i+1))
      = (∑ i ∈ Finset.range 94, stT52 (i+1)) + stT52 95 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 94
    simpa using h
  have hprev := st52_p94
  have hstep := st52_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p96 : ((4051187334911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT52 (i+1))
      = (∑ i ∈ Finset.range 95, stT52 (i+1)) + stT52 96 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 95
    simpa using h
  have hprev := st52_p95
  have hstep := st52_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p97 : ((4153245853447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT52 (i+1))
      = (∑ i ∈ Finset.range 96, stT52 (i+1)) + stT52 97 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 96
    simpa using h
  have hprev := st52_p96
  have hstep := st52_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p98 : ((4358233978503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT52 (i+1))
      = (∑ i ∈ Finset.range 97, stT52 (i+1)) + stT52 98 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 97
    simpa using h
  have hprev := st52_p97
  have hstep := st52_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p99 : ((18433322607813/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT52 (i+1))
      = (∑ i ∈ Finset.range 98, stT52 (i+1)) + stT52 99 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 98
    simpa using h
  have hprev := st52_p98
  have hstep := st52_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st52_p100 : ((4835880674403/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT52 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT52 (i+1))
      = (∑ i ∈ Finset.range 99, stT52 (i+1)) + stT52 100 := by
    have h := Finset.sum_range_succ (fun i => stT52 (i+1)) 99
    simpa using h
  have hprev := st52_p99
  have hstep := st52_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 52`.** -/
theorem station_52_sign : hardyG (((52:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 52 100 (by norm_num) (by norm_num)
    ((280901/1000000 : ℚ) : ℝ)
  have hchain := st52_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT52 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((52:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((280901/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((52:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((52:ℕ)):ℝ)+1) * ((((52:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2518803/5200000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((4835880674403/2500000000000 : ℚ) : ℝ) - ((2518803/5200000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((280901/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((52:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((280901/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((52:ℕ)):ℝ))).re
      - Real.sin ((280901/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((52:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((52:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((52:ℕ)):ℝ)
      = ((((52:ℕ)):ℝ) * (Real.log (((52:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((52:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_52
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
  have hθwin : |(((280901/1000000 : ℚ) : ℝ) + ((5:ℤ)) * (2*Real.pi) - Real.pi) - theta (((52:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((52:ℕ)):ℝ))
    (φ := ((280901/1000000 : ℚ) : ℝ) + ((5:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((280901/1000000 : ℚ) : ℝ) + ((5:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((280901/1000000 : ℚ)) : ℝ) - Real.pi) + ((5:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((280901/1000000 : ℚ)) : ℝ) - Real.pi) 5).1,
    (cos_sin_shift ((((280901/1000000 : ℚ)) : ℝ) - Real.pi) 5).2]
  exact cos_sin_flip ((280901/1000000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_52_sign
end AxiomAudit
