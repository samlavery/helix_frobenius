import RequestProject.DVPSqrtTable
import RequestProject.DVPLog200Table

/-!
# Station `t = 115` of the extended Hardy ladder (rung-126)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT115 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((115 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-138519/200000 : ℚ) : ℝ))

theorem st115_c1 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((96199/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1731487/10000000) (δ := 21/100000000) (ψ := -138519/200000) 115 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t1 : ((384771/500000 : ℚ) : ℝ) ≤ stT115 1 := by
  have hc : ((384771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((384771/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((384771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c2 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((57939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3192221/10000000) (δ := 911/100000000) (ψ := -138519/200000) 115 13
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t2 : ((409619840243/2000000000000 : ℚ) : ℝ) ≤ stT115 2 := by
  have hc : ((57929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((409619840243/2000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((57929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c3 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((100067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 684651/2000000) (δ := 127/12500000) (ψ := -138519/200000) 115 20
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t3 : ((144398171771/1250000000000 : ℚ) : ℝ) ≤ stT115 3 := by
  have hc : ((50021/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144398171771/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((50021/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c4 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-248629/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3796017/5000000) (δ := 679/100000000) (ψ := -138519/200000) 115 25
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t4 : ((-2486415497283/5000000000000 : ℚ) : ℝ) ≤ stT115 4 := by
  have hc : ((-497283/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).2
  have h0 : (0:ℝ) ≤ ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2486415497283/5000000000000 : ℚ) : ℝ)
      = ((5000001/10000000 : ℚ) : ℝ) * ((-497283/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c5 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-182291/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6794011/10000000) (δ := 51/5000000) (ψ := -138519/200000) 115 30
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t5 : ((-101909358117/250000000000 : ℚ) : ℝ) ≤ stT115 5 := by
  have hc : ((-182301/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101909358117/250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-182301/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c6 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((825233/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1500453/10000000) (δ := 159/20000000) (ψ := -138519/200000) 115 33
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t6 : ((1684397372103/5000000000000 : ℚ) : ℝ) ≤ stT115 6 := by
  have hc : ((825183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1684397372103/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((825183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c7 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-151033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4306023/10000000) (δ := 77/12500000) (ψ := -138519/200000) 115 36
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t7 : ((-114208021107/2000000000000 : ℚ) : ℝ) ≤ stT115 7 := by
  have hc : ((-151083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114208021107/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-151083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c8 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((15077/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1334163/5000000) (δ := 347/50000000) (ψ := -138519/200000) 115 38
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t8 : ((852795308331/5000000000000 : ℚ) : ℝ) ≤ stT115 8 := by
  have hc : ((241207/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((852795308331/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((241207/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c9 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-457527/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2557511/5000000) (δ := 43/5000000) (ψ := -138519/200000) 115 40
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t9 : ((-762628485859/5000000000000 : ℚ) : ℝ) ≤ stT115 9 := by
  have hc : ((-457577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).2
  have h0 : (0:ℝ) ≤ ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-762628485859/5000000000000 : ℚ) : ℝ)
      = ((1666667/5000000 : ℚ) : ℝ) * ((-457577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c10 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-25299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 997561/2500000) (δ := 263/25000000) (ψ := -138519/200000) 115 42
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t10 : ((-40080292511/5000000000000 : ℚ) : ℝ) ≤ stT115 10 := by
  have hc : ((-25349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40080292511/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-25349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c11 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((499977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -12003/5000000) (δ := 813/100000000) (ψ := -138519/200000) 115 44
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t11 : ((94213235911/312500000000 : ℚ) : ℝ) ≤ stT115 11 := by
  have hc : ((31247/31250 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94213235911/312500000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((31247/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c12 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-840859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3212081/5000000) (δ := 309/50000000) (ψ := -138519/200000) 115 46
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t12 : ((-75859241799/312500000000 : ℚ) : ℝ) ≤ stT115 12 := by
  have hc : ((-840909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75859241799/312500000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-840909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c13 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((117333/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 440077/5000000) (δ := 131/20000000) (ψ := -138519/200000) 115 47
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t13 : ((2603245929/10000000000 : ℚ) : ℝ) ≤ stT115 13 := by
  have hc : ((469307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2603245929/10000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((469307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c14 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-53273/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 809779/1250000) (δ := 847/100000000) (ψ := -138519/200000) 115 48
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t14 : ((-1139091714117/5000000000000 : ℚ) : ℝ) ≤ stT115 14 := by
  have hc : ((-426209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1139091714117/5000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-426209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c15 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-452977/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1275561/2500000) (δ := 147/12500000) (ψ := -138519/200000) 115 50
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t15 : ((-1169710730703/10000000000000 : ℚ) : ℝ) ≤ stT115 15 := by
  have hc : ((-453027/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1169710730703/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-453027/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c16 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((309961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1127691/5000000) (δ := 183/20000000) (ψ := -138519/200000) 115 51
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t16 : ((19371/125000 : ℚ) : ℝ) ≤ stT115 16 := by
  have hc : ((19371/31250 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19371/125000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((19371/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c17 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((488647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -533767/10000000) (δ := 171/25000000) (ψ := -138519/200000) 115 52
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t17 : ((148135287429/625000000000 : ℚ) : ℝ) ≤ stT115 17 := by
  have hc : ((244311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((148135287429/625000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((244311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c18 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((997073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 95657/5000000) (δ := 1/156250) (ψ := -138519/200000) 115 53
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t18 : ((1175002572753/5000000000000 : ℚ) : ℝ) ≤ stT115 18 := by
  have hc : ((997023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1175002572753/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((997023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c19 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((999939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 27677/10000000) (δ := 89/10000000) (ψ := -138519/200000) 115 54
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t19 : ((2293902348573/10000000000000 : ℚ) : ℝ) ≤ stT115 19 := by
  have hc : ((999889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2293902348573/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((999889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c20 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((465549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -116683/1250000) (δ := 831/100000000) (ψ := -138519/200000) 115 55
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t20 : ((260235713527/1250000000000 : ℚ) : ℝ) ≤ stT115 20 := by
  have hc : ((116381/125000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((260235713527/1250000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((116381/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c21 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((100259/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -522851/2000000) (δ := 731/100000000) (ψ := -138519/200000) 115 56
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t21 : ((109380581161/1000000000000 : ℚ) : ℝ) ≤ stT115 21 := by
  have hc : ((100249/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109380581161/1000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((100249/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c22 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-4963/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2473857/5000000) (δ := 37/6250000) (ψ := -138519/200000) 115 57
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t22 : ((-10582488209/125000000000 : ℚ) : ℝ) ≤ stT115 22 := by
  have hc : ((-39709/100000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10582488209/125000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-39709/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c23 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-499981/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 979021/1250000) (δ := 981/100000000) (ψ := -138519/200000) 115 57
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t23 : ((-104258501087/500000000000 : ℚ) : ℝ) ≤ stT115 23 := by
  have hc : ((-250003/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104258501087/500000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-250003/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c24 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-21547/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2180047/5000000) (δ := 81/10000000) (ψ := -138519/200000) 115 58
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t24 : ((-87990798273/2500000000000 : ℚ) : ℝ) ≤ stT115 24 := by
  have hc : ((-86213/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87990798273/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-86213/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c25 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((987953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 194227/5000000) (δ := 879/100000000) (ψ := -138519/200000) 115 59
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t25 : ((987903/5000000 : ℚ) : ℝ) ≤ stT115 25 := by
  have hc : ((987903/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((987903/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((987903/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c26 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-2913/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2021777/5000000) (δ := 359/50000000) (ψ := -138519/200000) 115 60
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t26 : ((-22875974149/2500000000000 : ℚ) : ℝ) ≤ stT115 26 := by
  have hc : ((-23329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22875974149/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-23329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c27 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-456773/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 680679/1000000) (δ := 149/20000000) (ψ := -138519/200000) 115 60
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t27 : ((-439554103899/2500000000000 : ℚ) : ℝ) ≤ stT115 27 := by
  have hc : ((-228399/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-439554103899/2500000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-228399/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c28 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((406413/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 388631/2500000) (δ := 267/25000000) (ψ := -138519/200000) 115 61
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t28 : ((96000122867/625000000000 : ℚ) : ℝ) ≤ stT115 28 := by
  have hc : ((101597/125000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96000122867/625000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((101597/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c29 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-55049/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1016171/2500000) (δ := 807/100000000) (ψ := -138519/200000) 115 62
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t29 : ((-51158154223/5000000000000 : ℚ) : ℝ) ≤ stT115 29 := by
  have hc : ((-55099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51158154223/5000000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-55099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c30 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-645753/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1420503/2500000) (δ := 117/12500000) (ψ := -138519/200000) 115 62
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t30 : ((-589534830413/5000000000000 : ℚ) : ℝ) ≤ stT115 30 := by
  have hc : ((-645803/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-589534830413/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-645803/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c31 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((194289/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -299439/5000000) (δ := 71/6250000) (ψ := -138519/200000) 115 63
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t31 : ((348935380787/2000000000000 : ℚ) : ℝ) ≤ stT115 31 := by
  have hc : ((194279/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348935380787/2000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((194279/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c32 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-481891/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -717909/1000000) (δ := 71/6250000) (ψ := -138519/200000) 115 64
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t32 : ((-212978800393/1250000000000 : ℚ) : ℝ) ≤ stT115 32 := by
  have hc : ((-120479/125000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-212978800393/1250000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-120479/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c33 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((49101/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 833881/5000000) (δ := 697/100000000) (ψ := -138519/200000) 115 64
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t33 : ((85468402451/625000000000 : ℚ) : ℝ) ≤ stT115 33 := by
  have hc : ((392783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85468402451/625000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((392783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c34 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-71833/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -218299/400000) (δ := 181/20000000) (ψ := -138519/200000) 115 65
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t34 : ((-246406616001/2500000000000 : ℚ) : ℝ) ≤ stT115 34 := by
  have hc : ((-287357/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-246406616001/2500000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-287357/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c35 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((407961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1438221/5000000) (δ := 339/50000000) (ψ := -138519/200000) 115 65
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t35 : ((172373806647/2500000000000 : ℚ) : ℝ) ≤ stT115 35 := by
  have hc : ((407911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((172373806647/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((407911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c36 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-316617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2366197/5000000) (δ := 367/50000000) (ψ := -138519/200000) 115 66
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t36 : ((-527778438889/10000000000000 : ℚ) : ℝ) ≤ stT115 36 := by
  have hc : ((-316667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).2
  have h0 : (0:ℝ) ≤ ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-527778438889/10000000000000 : ℚ) : ℝ)
      = ((1666667/10000000 : ℚ) : ℝ) * ((-316667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c37 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((19237/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3144811/10000000) (δ := 517/50000000) (ψ := -138519/200000) 115 66
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t37 : ((252962231419/5000000000000 : ℚ) : ℝ) ≤ stT115 37 := by
  have hc : ((153871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((252962231419/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((153871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c38 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-188991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4896031/10000000) (δ := 67/10000000) (ψ := -138519/200000) 115 67
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t38 : ((-7665614761/125000000000 : ℚ) : ℝ) ≤ stT115 38 := by
  have hc : ((-23627/62500 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7665614761/125000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-23627/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c39 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((257937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2571921/10000000) (δ := 653/100000000) (ψ := -138519/200000) 115 67
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t39 : ((51623698159/625000000000 : ℚ) : ℝ) ≤ stT115 39 := by
  have hc : ((32239/62500 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51623698159/625000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((32239/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c40 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-348811/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1464293/2500000) (δ := 61/10000000) (ψ := -138519/200000) 115 68
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t40 : ((-137889551051/1250000000000 : ℚ) : ℝ) ≤ stT115 40 := by
  have hc : ((-87209/125000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-137889551051/1250000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-87209/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c41 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((879121/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 620977/5000000) (δ := 3/400000) (ψ := -138519/200000) 115 68
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t41 : ((1372877706327/10000000000000 : ℚ) : ℝ) ≤ stT115 41 := by
  have hc : ((879071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1372877706327/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((879071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c42 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-992021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7537963/10000000) (δ := 119/12500000) (ψ := -138519/200000) 115 69
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t42 : ((-765399641707/5000000000000 : ℚ) : ℝ) ≤ stT115 42 := by
  have hc : ((-992071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-765399641707/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-992071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c43 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((119073/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -154589/2000000) (δ := 491/50000000) (ψ := -138519/200000) 115 69
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t43 : ((145260006199/1000000000000 : ℚ) : ℝ) ≤ stT115 43 := by
  have hc : ((476267/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((145260006199/1000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((476267/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c44 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-138337/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5836541/10000000) (δ := 99/12500000) (ψ := -138519/200000) 115 69
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t44 : ((-208565988279/2000000000000 : ℚ) : ℝ) ≤ stT115 44 := by
  have hc : ((-138347/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-208565988279/2000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-138347/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c45 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((205139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -852619/2500000) (δ := 253/25000000) (ψ := -138519/200000) 115 70
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t45 : ((305728428279/10000000000000 : ℚ) : ℝ) ≤ stT115 45 := by
  have hc : ((205089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305728428279/10000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((205089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c46 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((79247/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 145423/500000) (δ := 551/50000000) (ψ := -138519/200000) 115 70
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t46 : ((116828538303/2000000000000 : ℚ) : ℝ) ≤ stT115 46 := by
  have hc : ((79237/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((116828538303/2000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((79237/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c47 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-439983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -661647/1000000) (δ := 1171/100000000) (ψ := -138519/200000) 115 71
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t47 : ((-1604544173/12500000000 : ℚ) : ℝ) ≤ stT115 47 := by
  have hc : ((-55001/62500 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1604544173/12500000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-55001/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c48 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((194939/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -281807/5000000) (δ := 1031/100000000) (ψ := -138519/200000) 115 71
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t48 : ((2250845163/16000000000 : ℚ) : ℝ) ≤ stT115 48 := by
  have hc : ((194929/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2250845163/16000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((194929/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c49 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-108763/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5364431/10000000) (δ := 561/50000000) (ψ := -138519/200000) 115 71
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t49 : ((-38847515539/500000000000 : ℚ) : ℝ) ≤ stT115 49 := by
  have hc : ((-108773/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38847515539/500000000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-108773/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c50 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-15057/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2267627/5000000) (δ := 11/1000000) (ψ := -138519/200000) 115 72
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t50 : ((-85192958467/2500000000000 : ℚ) : ℝ) ≤ stT115 50 := by
  have hc : ((-120481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85192958467/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-120481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c51 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((894627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1158001/10000000) (δ := 1/125000) (ψ := -138519/200000) 115 72
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t51 : ((31316457039/250000000000 : ℚ) : ℝ) ≤ stT115 51 := by
  have hc : ((894577/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((31316457039/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((894577/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c52 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-225619/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6740701/10000000) (δ := 19/2000000) (ψ := -138519/200000) 115 72
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t52 : ((-625789416513/5000000000000 : ℚ) : ℝ) ≤ stT115 52 := by
  have hc : ((-451263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-625789416513/5000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-451263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c53 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((173551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1745453/5000000) (δ := 999/100000000) (ψ := -138519/200000) 115 73
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t53 : ((47664368221/2000000000000 : ℚ) : ℝ) ≤ stT115 53 := by
  have hc : ((173501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47664368221/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((173501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c54 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((729481/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 941541/5000000) (δ := 629/100000000) (ψ := -138519/200000) 115 73
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t54 : ((992629399437/10000000000000 : ℚ) : ℝ) ≤ stT115 54 := by
  have hc : ((729431/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((992629399437/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((729431/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c55 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-961549/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7158459/10000000) (δ := 477/50000000) (ψ := -138519/200000) 115 73
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t55 : ((-3241550229/25000000000 : ℚ) : ℝ) ≤ stT115 55 := by
  have hc : ((-961599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3241550229/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-961599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c56 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((55319/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -105287/312500) (δ := 203/20000000) (ψ := -138519/200000) 115 74
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t56 : ((73906407789/2500000000000 : ℚ) : ℝ) ≤ stT115 56 := by
  have hc : ((110613/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((73906407789/2500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((110613/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c57 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((386329/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 343889/2000000) (δ := 31/4000000) (ψ := -138519/200000) 115 74
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t57 : ((499679697/4882812500 : ℚ) : ℝ) ≤ stT115 57 := by
  have hc : ((12072/15625 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499679697/4882812500 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((12072/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c58 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-898803/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6719571/10000000) (δ := 519/50000000) (ψ := -138519/200000) 115 74
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t58 : ((-236050482889/2000000000000 : ℚ) : ℝ) ≤ stT115 58 := by
  have hc : ((-898853/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236050482889/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-898853/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c59 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-58667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4073743/10000000) (δ := 167/25000000) (ψ := -138519/200000) 115 75
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t59 : ((-7644307513/1000000000000 : ℚ) : ℝ) ≤ stT115 59 := by
  have hc : ((-58717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7644307513/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-58717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c60 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((19087/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 23697/312500) (δ := 143/20000000) (ψ := -138519/200000) 115 75
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t60 : ((6159977871/50000000000 : ℚ) : ℝ) ≤ stT115 60 := by
  have hc : ((9543/10000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6159977871/50000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((9543/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c61 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-118377/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2755239/5000000) (δ := 29/4000000) (ψ := -138519/200000) 115 75
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t61 : ((-151579044803/2000000000000 : ℚ) : ℝ) ≤ stT115 61 := by
  have hc : ((-118387/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-151579044803/2000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-118387/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c62 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-595781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2761293/5000000) (δ := 473/50000000) (ψ := -138519/200000) 115 76
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t62 : ((-378353280831/5000000000000 : ℚ) : ℝ) ≤ stT115 62 := by
  have hc : ((-595831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378353280831/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-595831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c63 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((93269/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -115311/1250000) (δ := 887/100000000) (ψ := -138519/200000) 115 76
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t63 : ((7343846349/62500000000 : ℚ) : ℝ) ≤ stT115 63 := by
  have hc : ((5829/6250 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7343846349/62500000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((5829/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c64 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((1027/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 721033/2000000) (δ := 117/12500000) (ψ := -138519/200000) 115 76
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t64 : ((5133/320000 : ℚ) : ℝ) ≤ stT115 64 := by
  have hc : ((5133/40000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5133/320000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((5133/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c65 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-24913/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1529069/2000000) (δ := 767/100000000) (ψ := -138519/200000) 115 77
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t65 : ((-30902340159/250000000000 : ℚ) : ℝ) ≤ stT115 65 := by
  have hc : ((-99657/100000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30902340159/250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-99657/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c66 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((132603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1627973/5000000) (δ := 169/25000000) (ψ := -138519/200000) 115 77
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t66 : ((40798029073/1250000000000 : ℚ) : ℝ) ≤ stT115 66 := by
  have hc : ((66289/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40798029073/1250000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((66289/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c67 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((455111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1067443/10000000) (δ := 483/50000000) (ψ := -138519/200000) 115 77
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t67 : ((138993958921/1250000000000 : ℚ) : ℝ) ≤ stT115 67 := by
  have hc : ((227543/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138993958921/1250000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((227543/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c68 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-106223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5326781/10000000) (δ := 137/12500000) (ψ := -138519/200000) 115 77
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t68 : ((-128826528207/2000000000000 : ℚ) : ℝ) ≤ stT115 68 := by
  have hc : ((-106233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-128826528207/2000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-106233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c69 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-392537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1546007/2500000) (δ := 9/800000) (ψ := -138519/200000) 115 78
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t69 : ((-236294648379/2500000000000 : ℚ) : ℝ) ≤ stT115 69 := by
  have hc : ((-196281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-236294648379/2500000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-196281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c70 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((34151/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1023633/5000000) (δ := 139/20000000) (ψ := -138519/200000) 115 78
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t70 : ((20407621679/250000000000 : ℚ) : ℝ) ≤ stT115 70 := by
  have hc : ((68297/100000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20407621679/250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((68297/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c71 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((687811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2030817/10000000) (δ := 439/50000000) (ψ := -138519/200000) 115 78
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t71 : ((816221687341/10000000000000 : ℚ) : ℝ) ≤ stT115 71 := by
  have hc : ((687761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((816221687341/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((687761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c72 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-375623/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6051861/10000000) (δ := 193/20000000) (ψ := -138519/200000) 115 78
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t72 : ((-864659523/9765625000 : ℚ) : ℝ) ≤ stT115 72 := by
  have hc : ((-11739/15625 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-864659523/9765625000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-11739/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c73 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-162087/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2845261/5000000) (δ := 141/20000000) (ψ := -138519/200000) 115 79
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t73 : ((-94861599997/1250000000000 : ℚ) : ℝ) ≤ stT115 73 := by
  have hc : ((-324199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-94861599997/1250000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-324199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c74 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((151469/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1778897/10000000) (δ := 131/12500000) (ψ := -138519/200000) 115 79
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t74 : ((44016863121/500000000000 : ℚ) : ℝ) ≤ stT115 74 := by
  have hc : ((151459/200000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44016863121/500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((151459/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c75 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((673333/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2080221/10000000) (δ := 207/20000000) (ψ := -138519/200000) 115 79
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t75 : ((7774398801/100000000000 : ℚ) : ℝ) ≤ stT115 75 := by
  have hc : ((673283/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7774398801/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((673283/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c76 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-706467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 184007/312500) (δ := 143/20000000) (ψ := -138519/200000) 115 79
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t76 : ((-810430813843/10000000000000 : ℚ) : ℝ) ≤ stT115 76 := by
  have hc : ((-706517/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-810430813843/10000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-706517/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c77 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-75379/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1515379/2500000) (δ := 467/50000000) (ψ := -138519/200000) 115 80
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t77 : ((-5369253669/62500000000 : ℚ) : ℝ) ≤ stT115 77 := by
  have hc : ((-9423/12500 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5369253669/62500000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-9423/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c78 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((589211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2351787/10000000) (δ := 437/50000000) (ψ := -138519/200000) 115 80
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t78 : ((667093449597/10000000000000 : ℚ) : ℝ) ≤ stT115 78 := by
  have hc : ((589161/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((667093449597/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((589161/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c79 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((108211/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1310683/10000000) (δ := 579/100000000) (ψ := -138519/200000) 115 80
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t79 : ((486959030253/5000000000000 : ℚ) : ℝ) ≤ stT115 79 := by
  have hc : ((432819/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((486959030253/5000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((432819/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c80 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-97363/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4927083/10000000) (δ := 387/50000000) (ψ := -138519/200000) 115 80
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t80 : ((-108869119767/2500000000000 : ℚ) : ℝ) ≤ stT115 80 := by
  have hc : ((-194751/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108869119767/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-194751/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c81 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-483473/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3604703/5000000) (δ := 3/500000) (ψ := -138519/200000) 115 81
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t81 : ((-33576276861/312500000000 : ℚ) : ℝ) ≤ stT115 81 := by
  have hc : ((-241749/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33576276861/312500000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-241749/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c82 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((97937/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1840877/5000000) (δ := 623/100000000) (ψ := -138519/200000) 115 81
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t82 : ((21619616481/2000000000000 : ℚ) : ℝ) ≤ stT115 82 := by
  have hc : ((97887/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21619616481/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((97887/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c83 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((996901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -196863/10000000) (δ := 1083/100000000) (ψ := -138519/200000) 115 81
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t83 : ((547092762671/5000000000000 : ℚ) : ℝ) ≤ stT115 83 := by
  have hc : ((996851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((547092762671/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((996851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c84 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((4202/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 811573/2500000) (δ := 1183/100000000) (ψ := -138519/200000) 115 81
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t84 : ((146684914071/5000000000000 : ℚ) : ℝ) ≤ stT115 84 := by
  have hc : ((134439/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146684914071/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((134439/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c85 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-886017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6648699/10000000) (δ := 13/2000000) (ψ := -138519/200000) 115 81
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t85 : ((-961075229751/10000000000000 : ℚ) : ℝ) ≤ stT115 85 := by
  have hc : ((-886067/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-961075229751/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-886067/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c86 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-650213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5696653/10000000) (δ := 11/1000000) (ψ := -138519/200000) 115 82
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t86 : ((-87649600033/1250000000000 : ℚ) : ℝ) ≤ stT115 86 := by
  have hc : ((-650263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87649600033/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-650263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c87 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((582361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2372917/10000000) (δ := 963/100000000) (ψ := -138519/200000) 115 82
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t87 : ((39018913177/625000000000 : ℚ) : ℝ) ≤ stT115 87 := by
  have hc : ((582311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39018913177/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((582311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c88 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((233519/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 912833/10000000) (δ := 1013/100000000) (ψ := -138519/200000) 115 82
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t88 : ((497837259039/5000000000000 : ℚ) : ℝ) ≤ stT115 88 := by
  have hc : ((467013/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497837259039/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((467013/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c89 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-5853/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 832291/2000000) (δ := 77/10000000) (ψ := -138519/200000) 115 82
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t89 : ((-24829923151/2500000000000 : ℚ) : ℝ) ≤ stT115 89 := by
  have hc : ((-46849/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24829923151/2500000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-46849/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c90 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-981609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7373779/10000000) (δ := 39/5000000) (ψ := -138519/200000) 115 82
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t90 : ((-1034759880287/10000000000000 : ℚ) : ℝ) ≤ stT115 90 := by
  have hc : ((-981659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1034759880287/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-981659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c91 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-236259/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1289339/2500000) (δ := 1211/100000000) (ψ := -138519/200000) 115 83
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t91 : ((-12384648647/250000000000 : ℚ) : ℝ) ≤ stT115 91 := by
  have hc : ((-59071/125000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12384648647/250000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-59071/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c92 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((346159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -125953/625000) (δ := 881/100000000) (ψ := -138519/200000) 115 83
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t92 : ((45108702081/625000000000 : ℚ) : ℝ) ≤ stT115 92 := by
  have hc : ((173067/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45108702081/625000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((173067/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c93 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((905959/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109289/1000000) (δ := 1051/100000000) (ψ := -138519/200000) 115 83
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t93 : ((939383243459/10000000000000 : ℚ) : ℝ) ≤ stT115 93 := by
  have hc : ((905909/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((939383243459/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((905909/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c94 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-96169/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2083893/5000000) (δ := 941/100000000) (ψ := -138519/200000) 115 83
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t94 : ((-49621196709/5000000000000 : ℚ) : ℝ) ≤ stT115 94 := by
  have hc : ((-96219/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-49621196709/5000000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-96219/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c95 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-967021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3605071/5000000) (δ := 1031/100000000) (ψ := -138519/200000) 115 83
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t95 : ((-992194537509/10000000000000 : ℚ) : ℝ) ≤ stT115 95 := by
  have hc : ((-967071/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-992194537509/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-967071/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c96 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-292197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2743661/5000000) (δ := 263/25000000) (ψ := -138519/200000) 115 84
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t96 : ((-149123954931/2500000000000 : ℚ) : ℝ) ≤ stT115 96 := by
  have hc : ((-146111/250000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-149123954931/2500000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-146111/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c97 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((336/625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2508021/10000000) (δ := 223/25000000) (ψ := -138519/200000) 115 84
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t97 : ((5457992423/100000000000 : ℚ) : ℝ) ≤ stT115 97 := by
  have hc : ((10751/20000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5457992423/100000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((10751/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c98 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((984501/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 440723/10000000) (δ := 451/50000000) (ψ := -138519/200000) 115 84
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t98 : ((124305643319/1250000000000 : ℚ) : ℝ) ≤ stT115 98 := by
  have hc : ((984451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124305643319/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((984451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c99 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((225041/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3359529/10000000) (δ := 611/100000000) (ψ := -138519/200000) 115 84
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t99 : ((226124279667/10000000000000 : ℚ) : ℝ) ≤ stT115 99 := by
  have hc : ((224991/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226124279667/10000000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((224991/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_c100 :
    |Real.cos (((115 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-138519/200000 : ℚ) : ℝ))
      - ((-100113/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6249001/10000000) (δ := 243/25000000) (ψ := -138519/200000) 115 84
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st115_t100 : ((-400477/5000000 : ℚ) : ℝ) ≤ stT115 100 := by
  have hc : ((-400477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((115 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-138519/200000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st115_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400477/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-400477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st115_p1 : ((384771/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT115 (i+1) := by
  rw [Finset.sum_range_one]
  exact st115_t1

theorem st115_p2 : ((1948703840243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT115 (i+1))
      = (∑ i ∈ Finset.range 1, stT115 (i+1)) + stT115 2 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 1
    simpa using h
  have hprev := st115_p1
  have hstep := st115_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p3 : ((10898704575383/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT115 (i+1))
      = (∑ i ∈ Finset.range 2, stT115 (i+1)) + stT115 3 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 2
    simpa using h
  have hprev := st115_p2
  have hstep := st115_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p4 : ((5925873580817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT115 (i+1))
      = (∑ i ∈ Finset.range 3, stT115 (i+1)) + stT115 4 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 3
    simpa using h
  have hprev := st115_p3
  have hstep := st115_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p5 : ((1849499256137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT115 (i+1))
      = (∑ i ∈ Finset.range 4, stT115 (i+1)) + stT115 5 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 4
    simpa using h
  have hprev := st115_p4
  have hstep := st115_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p6 : ((5218294000343/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT115 (i+1))
      = (∑ i ∈ Finset.range 5, stT115 (i+1)) + stT115 6 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 5
    simpa using h
  have hprev := st115_p5
  have hstep := st115_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p7 : ((580906736851/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT115 (i+1))
      = (∑ i ∈ Finset.range 6, stT115 (i+1)) + stT115 7 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 6
    simpa using h
  have hprev := st115_p6
  have hstep := st115_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p8 : ((635284451147/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT115 (i+1))
      = (∑ i ∈ Finset.range 7, stT115 (i+1)) + stT115 8 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 7
    simpa using h
  have hprev := st115_p7
  have hstep := st115_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p9 : ((603448442469/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT115 (i+1))
      = (∑ i ∈ Finset.range 8, stT115 (i+1)) + stT115 9 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 8
    simpa using h
  have hprev := st115_p8
  have hstep := st115_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p10 : ((474742695473/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT115 (i+1))
      = (∑ i ∈ Finset.range 9, stT115 (i+1)) + stT115 10 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 9
    simpa using h
  have hprev := st115_p9
  have hstep := st115_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p11 : ((3881125251941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT115 (i+1))
      = (∑ i ∈ Finset.range 10, stT115 (i+1)) + stT115 11 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 10
    simpa using h
  have hprev := st115_p10
  have hstep := st115_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p12 : ((2667377383157/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT115 (i+1))
      = (∑ i ∈ Finset.range 11, stT115 (i+1)) + stT115 12 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 11
    simpa using h
  have hprev := st115_p11
  have hstep := st115_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p13 : ((3969000347657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT115 (i+1))
      = (∑ i ∈ Finset.range 12, stT115 (i+1)) + stT115 13 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 12
    simpa using h
  have hprev := st115_p12
  have hstep := st115_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p14 : ((141495431677/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT115 (i+1))
      = (∑ i ∈ Finset.range 13, stT115 (i+1)) + stT115 14 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 13
    simpa using h
  have hprev := st115_p13
  have hstep := st115_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p15 : ((4490106536377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT115 (i+1))
      = (∑ i ∈ Finset.range 14, stT115 (i+1)) + stT115 15 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 14
    simpa using h
  have hprev := st115_p14
  have hstep := st115_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p16 : ((6039786536377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT115 (i+1))
      = (∑ i ∈ Finset.range 15, stT115 (i+1)) + stT115 16 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 15
    simpa using h
  have hprev := st115_p15
  have hstep := st115_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p17 : ((8409951135241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT115 (i+1))
      = (∑ i ∈ Finset.range 16, stT115 (i+1)) + stT115 17 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 16
    simpa using h
  have hprev := st115_p16
  have hstep := st115_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p18 : ((10759956280747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT115 (i+1))
      = (∑ i ∈ Finset.range 17, stT115 (i+1)) + stT115 18 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 17
    simpa using h
  have hprev := st115_p17
  have hstep := st115_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p19 : ((326346465733/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT115 (i+1))
      = (∑ i ∈ Finset.range 18, stT115 (i+1)) + stT115 19 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 18
    simpa using h
  have hprev := st115_p18
  have hstep := st115_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p20 : ((118248002637/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT115 (i+1))
      = (∑ i ∈ Finset.range 19, stT115 (i+1)) + stT115 20 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 19
    simpa using h
  have hprev := st115_p19
  have hstep := st115_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p21 : ((8114775074573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT115 (i+1))
      = (∑ i ∈ Finset.range 20, stT115 (i+1)) + stT115 21 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 20
    simpa using h
  have hprev := st115_p20
  have hstep := st115_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p22 : ((7691475546213/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT115 (i+1))
      = (∑ i ∈ Finset.range 21, stT115 (i+1)) + stT115 22 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 21
    simpa using h
  have hprev := st115_p21
  have hstep := st115_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p23 : ((6648890535343/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT115 (i+1))
      = (∑ i ∈ Finset.range 22, stT115 (i+1)) + stT115 23 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 22
    simpa using h
  have hprev := st115_p22
  have hstep := st115_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p24 : ((6472908938797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT115 (i+1))
      = (∑ i ∈ Finset.range 23, stT115 (i+1)) + stT115 24 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 23
    simpa using h
  have hprev := st115_p23
  have hstep := st115_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p25 : ((7460811938797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT115 (i+1))
      = (∑ i ∈ Finset.range 24, stT115 (i+1)) + stT115 25 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 24
    simpa using h
  have hprev := st115_p24
  have hstep := st115_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p26 : ((7415059990499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT115 (i+1))
      = (∑ i ∈ Finset.range 25, stT115 (i+1)) + stT115 26 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 25
    simpa using h
  have hprev := st115_p25
  have hstep := st115_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p27 : ((6535951782701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT115 (i+1))
      = (∑ i ∈ Finset.range 26, stT115 (i+1)) + stT115 27 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 26
    simpa using h
  have hprev := st115_p26
  have hstep := st115_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p28 : ((7303952765637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT115 (i+1))
      = (∑ i ∈ Finset.range 27, stT115 (i+1)) + stT115 28 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 27
    simpa using h
  have hprev := st115_p27
  have hstep := st115_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p29 : ((3626397305707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT115 (i+1))
      = (∑ i ∈ Finset.range 28, stT115 (i+1)) + stT115 29 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 28
    simpa using h
  have hprev := st115_p28
  have hstep := st115_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p30 : ((6663259781001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT115 (i+1))
      = (∑ i ∈ Finset.range 29, stT115 (i+1)) + stT115 30 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 29
    simpa using h
  have hprev := st115_p29
  have hstep := st115_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p31 : ((15071196465937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT115 (i+1))
      = (∑ i ∈ Finset.range 30, stT115 (i+1)) + stT115 31 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 30
    simpa using h
  have hprev := st115_p30
  have hstep := st115_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p32 : ((13367366062793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT115 (i+1))
      = (∑ i ∈ Finset.range 31, stT115 (i+1)) + stT115 32 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 31
    simpa using h
  have hprev := st115_p31
  have hstep := st115_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p33 : ((14734860502009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT115 (i+1))
      = (∑ i ∈ Finset.range 32, stT115 (i+1)) + stT115 33 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 32
    simpa using h
  have hprev := st115_p32
  have hstep := st115_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p34 : ((2749846807601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT115 (i+1))
      = (∑ i ∈ Finset.range 33, stT115 (i+1)) + stT115 34 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 33
    simpa using h
  have hprev := st115_p33
  have hstep := st115_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p35 : ((14438729264593/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT115 (i+1))
      = (∑ i ∈ Finset.range 34, stT115 (i+1)) + stT115 35 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 34
    simpa using h
  have hprev := st115_p34
  have hstep := st115_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p36 : ((1738868853213/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT115 (i+1))
      = (∑ i ∈ Finset.range 35, stT115 (i+1)) + stT115 36 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 35
    simpa using h
  have hprev := st115_p35
  have hstep := st115_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p37 : ((7208437644271/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT115 (i+1))
      = (∑ i ∈ Finset.range 36, stT115 (i+1)) + stT115 37 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 36
    simpa using h
  have hprev := st115_p36
  have hstep := st115_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p38 : ((6901813053831/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT115 (i+1))
      = (∑ i ∈ Finset.range 37, stT115 (i+1)) + stT115 38 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 37
    simpa using h
  have hprev := st115_p37
  have hstep := st115_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p39 : ((7314802639103/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT115 (i+1))
      = (∑ i ∈ Finset.range 38, stT115 (i+1)) + stT115 39 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 38
    simpa using h
  have hprev := st115_p38
  have hstep := st115_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p40 : ((6763244434899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT115 (i+1))
      = (∑ i ∈ Finset.range 39, stT115 (i+1)) + stT115 40 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 39
    simpa using h
  have hprev := st115_p39
  have hstep := st115_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p41 : ((119194932609/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT115 (i+1))
      = (∑ i ∈ Finset.range 40, stT115 (i+1)) + stT115 41 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 40
    simpa using h
  have hprev := st115_p40
  have hstep := st115_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p42 : ((13368567292711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT115 (i+1))
      = (∑ i ∈ Finset.range 41, stT115 (i+1)) + stT115 42 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 41
    simpa using h
  have hprev := st115_p41
  have hstep := st115_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p43 : ((14821167354701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT115 (i+1))
      = (∑ i ∈ Finset.range 42, stT115 (i+1)) + stT115 43 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 42
    simpa using h
  have hprev := st115_p42
  have hstep := st115_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p44 : ((6889168706653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT115 (i+1))
      = (∑ i ∈ Finset.range 43, stT115 (i+1)) + stT115 44 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 43
    simpa using h
  have hprev := st115_p43
  have hstep := st115_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p45 : ((2816813168317/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT115 (i+1))
      = (∑ i ∈ Finset.range 44, stT115 (i+1)) + stT115 45 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 44
    simpa using h
  have hprev := st115_p44
  have hstep := st115_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p46 : ((146682085331/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT115 (i+1))
      = (∑ i ∈ Finset.range 45, stT115 (i+1)) + stT115 46 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 45
    simpa using h
  have hprev := st115_p45
  have hstep := st115_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p47 : ((133845731947/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT115 (i+1))
      = (∑ i ∈ Finset.range 46, stT115 (i+1)) + stT115 47 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 46
    simpa using h
  have hprev := st115_p46
  have hstep := st115_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p48 : ((591654056863/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT115 (i+1))
      = (∑ i ∈ Finset.range 47, stT115 (i+1)) + stT115 48 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 47
    simpa using h
  have hprev := st115_p47
  have hstep := st115_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p49 : ((2802880222159/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT115 (i+1))
      = (∑ i ∈ Finset.range 48, stT115 (i+1)) + stT115 49 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 48
    simpa using h
  have hprev := st115_p48
  have hstep := st115_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p50 : ((13673629276927/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT115 (i+1))
      = (∑ i ∈ Finset.range 49, stT115 (i+1)) + stT115 50 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 49
    simpa using h
  have hprev := st115_p49
  have hstep := st115_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p51 : ((14926287558487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT115 (i+1))
      = (∑ i ∈ Finset.range 50, stT115 (i+1)) + stT115 51 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 50
    simpa using h
  have hprev := st115_p50
  have hstep := st115_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p52 : ((13674708725461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT115 (i+1))
      = (∑ i ∈ Finset.range 51, stT115 (i+1)) + stT115 52 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 51
    simpa using h
  have hprev := st115_p51
  have hstep := st115_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p53 : ((6956515283283/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT115 (i+1))
      = (∑ i ∈ Finset.range 52, stT115 (i+1)) + stT115 53 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 52
    simpa using h
  have hprev := st115_p52
  have hstep := st115_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p54 : ((14905659966003/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT115 (i+1))
      = (∑ i ∈ Finset.range 53, stT115 (i+1)) + stT115 54 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 53
    simpa using h
  have hprev := st115_p53
  have hstep := st115_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p55 : ((13609039874403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT115 (i+1))
      = (∑ i ∈ Finset.range 54, stT115 (i+1)) + stT115 55 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 54
    simpa using h
  have hprev := st115_p54
  have hstep := st115_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p56 : ((13904665505559/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT115 (i+1))
      = (∑ i ∈ Finset.range 55, stT115 (i+1)) + stT115 56 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 55
    simpa using h
  have hprev := st115_p55
  have hstep := st115_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p57 : ((2985601905003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT115 (i+1))
      = (∑ i ∈ Finset.range 56, stT115 (i+1)) + stT115 57 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 56
    simpa using h
  have hprev := st115_p56
  have hstep := st115_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p58 : ((1374775711057/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT115 (i+1))
      = (∑ i ∈ Finset.range 57, stT115 (i+1)) + stT115 58 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 57
    simpa using h
  have hprev := st115_p57
  have hstep := st115_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p59 : ((170891425443/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT115 (i+1))
      = (∑ i ∈ Finset.range 58, stT115 (i+1)) + stT115 59 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 58
    simpa using h
  have hprev := st115_p58
  have hstep := st115_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p60 : ((372582740241/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT115 (i+1))
      = (∑ i ∈ Finset.range 59, stT115 (i+1)) + stT115 60 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 59
    simpa using h
  have hprev := st115_p59
  have hstep := st115_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p61 : ((22632663017/16000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT115 (i+1))
      = (∑ i ∈ Finset.range 60, stT115 (i+1)) + stT115 61 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 60
    simpa using h
  have hprev := st115_p60
  have hstep := st115_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p62 : ((13388707823963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT115 (i+1))
      = (∑ i ∈ Finset.range 61, stT115 (i+1)) + stT115 62 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 61
    simpa using h
  have hprev := st115_p61
  have hstep := st115_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p63 : ((14563723239803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT115 (i+1))
      = (∑ i ∈ Finset.range 62, stT115 (i+1)) + stT115 63 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 62
    simpa using h
  have hprev := st115_p62
  have hstep := st115_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p64 : ((14724129489803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT115 (i+1))
      = (∑ i ∈ Finset.range 63, stT115 (i+1)) + stT115 64 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 63
    simpa using h
  have hprev := st115_p63
  have hstep := st115_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p65 : ((13488035883443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT115 (i+1))
      = (∑ i ∈ Finset.range 64, stT115 (i+1)) + stT115 65 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 64
    simpa using h
  have hprev := st115_p64
  have hstep := st115_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p66 : ((13814420116027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT115 (i+1))
      = (∑ i ∈ Finset.range 65, stT115 (i+1)) + stT115 66 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 65
    simpa using h
  have hprev := st115_p65
  have hstep := st115_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p67 : ((2985274357479/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT115 (i+1))
      = (∑ i ∈ Finset.range 66, stT115 (i+1)) + stT115 67 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 66
    simpa using h
  have hprev := st115_p66
  have hstep := st115_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p68 : ((357055978659/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT115 (i+1))
      = (∑ i ∈ Finset.range 67, stT115 (i+1)) + stT115 68 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 67
    simpa using h
  have hprev := st115_p67
  have hstep := st115_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p69 : ((3334265138211/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT115 (i+1))
      = (∑ i ∈ Finset.range 68, stT115 (i+1)) + stT115 69 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 68
    simpa using h
  have hprev := st115_p68
  have hstep := st115_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p70 : ((3538341355001/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT115 (i+1))
      = (∑ i ∈ Finset.range 69, stT115 (i+1)) + stT115 70 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 69
    simpa using h
  have hprev := st115_p69
  have hstep := st115_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p71 : ((2993917421469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT115 (i+1))
      = (∑ i ∈ Finset.range 70, stT115 (i+1)) + stT115 71 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 70
    simpa using h
  have hprev := st115_p70
  have hstep := st115_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p72 : ((14084175755793/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT115 (i+1))
      = (∑ i ∈ Finset.range 71, stT115 (i+1)) + stT115 72 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 71
    simpa using h
  have hprev := st115_p71
  have hstep := st115_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p73 : ((13325282955817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT115 (i+1))
      = (∑ i ∈ Finset.range 72, stT115 (i+1)) + stT115 73 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 72
    simpa using h
  have hprev := st115_p72
  have hstep := st115_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p74 : ((14205620218237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT115 (i+1))
      = (∑ i ∈ Finset.range 73, stT115 (i+1)) + stT115 74 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 73
    simpa using h
  have hprev := st115_p73
  have hstep := st115_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p75 : ((14983060098337/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT115 (i+1))
      = (∑ i ∈ Finset.range 74, stT115 (i+1)) + stT115 75 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 74
    simpa using h
  have hprev := st115_p74
  have hstep := st115_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p76 : ((7086314642247/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT115 (i+1))
      = (∑ i ∈ Finset.range 75, stT115 (i+1)) + stT115 76 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 75
    simpa using h
  have hprev := st115_p75
  have hstep := st115_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p77 : ((6656774348727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT115 (i+1))
      = (∑ i ∈ Finset.range 76, stT115 (i+1)) + stT115 77 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 76
    simpa using h
  have hprev := st115_p76
  have hstep := st115_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p78 : ((13980642147051/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT115 (i+1))
      = (∑ i ∈ Finset.range 77, stT115 (i+1)) + stT115 78 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 77
    simpa using h
  have hprev := st115_p77
  have hstep := st115_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p79 : ((14954560207557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT115 (i+1))
      = (∑ i ∈ Finset.range 78, stT115 (i+1)) + stT115 79 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 78
    simpa using h
  have hprev := st115_p78
  have hstep := st115_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p80 : ((14519083728489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT115 (i+1))
      = (∑ i ∈ Finset.range 79, stT115 (i+1)) + stT115 80 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 79
    simpa using h
  have hprev := st115_p79
  have hstep := st115_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p81 : ((13444642868937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT115 (i+1))
      = (∑ i ∈ Finset.range 80, stT115 (i+1)) + stT115 81 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 80
    simpa using h
  have hprev := st115_p80
  have hstep := st115_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p82 : ((6776370475671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT115 (i+1))
      = (∑ i ∈ Finset.range 81, stT115 (i+1)) + stT115 82 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 81
    simpa using h
  have hprev := st115_p81
  have hstep := st115_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p83 : ((3661731619171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT115 (i+1))
      = (∑ i ∈ Finset.range 82, stT115 (i+1)) + stT115 83 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 82
    simpa using h
  have hprev := st115_p82
  have hstep := st115_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p84 : ((7470148152413/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT115 (i+1))
      = (∑ i ∈ Finset.range 83, stT115 (i+1)) + stT115 84 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 83
    simpa using h
  have hprev := st115_p83
  have hstep := st115_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p85 : ((559168843003/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT115 (i+1))
      = (∑ i ∈ Finset.range 84, stT115 (i+1)) + stT115 85 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 84
    simpa using h
  have hprev := st115_p84
  have hstep := st115_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p86 : ((13278024274811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT115 (i+1))
      = (∑ i ∈ Finset.range 85, stT115 (i+1)) + stT115 86 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 85
    simpa using h
  have hprev := st115_p85
  have hstep := st115_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p87 : ((13902326885643/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT115 (i+1))
      = (∑ i ∈ Finset.range 86, stT115 (i+1)) + stT115 87 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 86
    simpa using h
  have hprev := st115_p86
  have hstep := st115_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p88 : ((14898001403721/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT115 (i+1))
      = (∑ i ∈ Finset.range 87, stT115 (i+1)) + stT115 88 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 87
    simpa using h
  have hprev := st115_p87
  have hstep := st115_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p89 : ((14798681711117/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT115 (i+1))
      = (∑ i ∈ Finset.range 88, stT115 (i+1)) + stT115 89 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 88
    simpa using h
  have hprev := st115_p88
  have hstep := st115_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p90 : ((1376392183083/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT115 (i+1))
      = (∑ i ∈ Finset.range 89, stT115 (i+1)) + stT115 90 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 89
    simpa using h
  have hprev := st115_p89
  have hstep := st115_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p91 : ((265370717699/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT115 (i+1))
      = (∑ i ∈ Finset.range 90, stT115 (i+1)) + stT115 91 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 90
    simpa using h
  have hprev := st115_p90
  have hstep := st115_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p92 : ((6995137559123/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT115 (i+1))
      = (∑ i ∈ Finset.range 91, stT115 (i+1)) + stT115 92 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 91
    simpa using h
  have hprev := st115_p91
  have hstep := st115_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p93 : ((2985931672341/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT115 (i+1))
      = (∑ i ∈ Finset.range 92, stT115 (i+1)) + stT115 93 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 92
    simpa using h
  have hprev := st115_p92
  have hstep := st115_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p94 : ((14830415968287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT115 (i+1))
      = (∑ i ∈ Finset.range 93, stT115 (i+1)) + stT115 94 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 93
    simpa using h
  have hprev := st115_p93
  have hstep := st115_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p95 : ((6919110715389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT115 (i+1))
      = (∑ i ∈ Finset.range 94, stT115 (i+1)) + stT115 95 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 94
    simpa using h
  have hprev := st115_p94
  have hstep := st115_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p96 : ((6620862805527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT115 (i+1))
      = (∑ i ∈ Finset.range 95, stT115 (i+1)) + stT115 96 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 95
    simpa using h
  have hprev := st115_p95
  have hstep := st115_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p97 : ((6893762426677/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT115 (i+1))
      = (∑ i ∈ Finset.range 96, stT115 (i+1)) + stT115 97 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 96
    simpa using h
  have hprev := st115_p96
  have hstep := st115_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p98 : ((7390984999953/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT115 (i+1))
      = (∑ i ∈ Finset.range 97, stT115 (i+1)) + stT115 98 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 97
    simpa using h
  have hprev := st115_p97
  have hstep := st115_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p99 : ((15008094279573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT115 (i+1))
      = (∑ i ∈ Finset.range 98, stT115 (i+1)) + stT115 99 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 98
    simpa using h
  have hprev := st115_p98
  have hstep := st115_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st115_p100 : ((14207140279573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT115 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT115 (i+1))
      = (∑ i ∈ Finset.range 99, stT115 (i+1)) + stT115 100 := by
    have h := Finset.sum_range_succ (fun i => stT115 (i+1)) 99
    simpa using h
  have hprev := st115_p99
  have hstep := st115_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 115`.** -/
theorem station_115_sign : hardyG (((115:ℕ)):ℝ) < 0 := by
  have hcore := phase_station_lower 115 100 (by norm_num) (by norm_num)
    ((-138519/200000 : ℚ) : ℝ)
  have hchain := st115_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT115 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((115:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-138519/200000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((115:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((115:ℕ)):ℝ)+1) * ((((115:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((5910639/4600000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((14207140279573/10000000000000 : ℚ) : ℝ) - ((5910639/4600000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-138519/200000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((115:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-138519/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((115:ℕ)):ℝ))).re
      - Real.sin ((-138519/200000 : ℚ) : ℝ)
        * (riemannZeta (line (((115:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((115:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((115:ℕ)):ℝ)
      = ((((115:ℕ)):ℝ) * (Real.log (((115:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((115:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_115
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
  have hθwin : |(((-138519/200000 : ℚ) : ℝ) + ((18:ℤ)) * (2*Real.pi) - Real.pi) - theta (((115:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((115:ℕ)):ℝ))
    (φ := ((-138519/200000 : ℚ) : ℝ) + ((18:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-138519/200000 : ℚ) : ℝ) + ((18:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-138519/200000 : ℚ)) : ℝ) - Real.pi) + ((18:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-138519/200000 : ℚ)) : ℝ) - Real.pi) 18).1,
    (cos_sin_shift ((((-138519/200000 : ℚ)) : ℝ) - Real.pi) 18).2]
  exact cos_sin_flip ((-138519/200000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_115_sign
end AxiomAudit
