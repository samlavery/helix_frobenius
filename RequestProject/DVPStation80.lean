import RequestProject.DVPSqrtTable

/-!
# Station `t = 80` of the extended Hardy ladder (rung-81)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT80 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((80 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))

theorem st80_c1 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((449/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 911443/2500000) (δ := 21/100000000) (ψ := -1458309/1000000) 80 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t1 : ((561/5000 : ℚ) : ℝ) ≤ stT80 1 := by
  have hc : ((561/5000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((561/5000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((561/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c2 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((935397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 903539/10000000) (δ := 319/50000000) (ψ := -1458309/1000000) 80 9
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t2 : ((6613901305249/10000000000000 : ℚ) : ℝ) ≤ stT80 2 := by
  have hc : ((935347/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6613901305249/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((935347/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c3 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((186991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 432093/1250000) (δ := 173/25000000) (ψ := -1458309/1000000) 80 14
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t3 : ((539652118691/5000000000000 : ℚ) : ℝ) ≤ stT80 3 := by
  have hc : ((186941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((539652118691/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((186941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c4 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((74151/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -367739/2000000) (δ := 227/50000000) (ψ := -1458309/1000000) 80 18
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t4 : ((37073/100000 : ℚ) : ℝ) ≤ stT80 4 := by
  have hc : ((37073/50000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37073/100000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((37073/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c5 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-40509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2166937/5000000) (δ := 179/25000000) (ψ := -1458309/1000000) 80 21
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t5 : ((-45304414731/625000000000 : ℚ) : ℝ) ≤ stT80 5 := by
  have hc : ((-81043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-45304414731/625000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-81043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c6 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((191887/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 714511/10000000) (δ := 137/25000000) (ψ := -1458309/1000000) 80 23
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t6 : ((391667199357/1000000000000 : ℚ) : ℝ) ≤ stT80 6 := by
  have hc : ((191877/200000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((391667199357/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((191877/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c7 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((39947/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1609/125000) (δ := 217/50000000) (ψ := -1458309/1000000) 80 25
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t7 : ((7548893979/20000000000 : ℚ) : ℝ) ≤ stT80 7 := by
  have hc : ((7989/8000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7548893979/20000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((7989/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c8 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-129301/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -71577/156250) (δ := 123/25000000) (ψ := -1458309/1000000) 80 27
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t8 : ((-114309117521/1250000000000 : ℚ) : ℝ) ≤ stT80 8 := by
  have hc : ((-64663/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-114309117521/1250000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-64663/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c9 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((32583/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 816929/2500000) (δ := 301/50000000) (ψ := -1458309/1000000) 80 28
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t9 : ((434356623231/5000000000000 : ℚ) : ℝ) ≤ stT80 9 := by
  have hc : ((130307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((434356623231/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((130307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c10 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-475991/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7076107/10000000) (δ := 743/100000000) (ψ := -1458309/1000000) 80 30
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t10 : ((-47040466389/156250000000 : ℚ) : ℝ) ≤ stT80 10 := by
  have hc : ((-29751/31250 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47040466389/156250000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-29751/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c11 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((81891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -744407/2000000) (δ := 277/50000000) (ψ := -1458309/1000000) 80 31
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t11 : ((246759863033/10000000000000 : ℚ) : ℝ) ≤ stT80 11 := by
  have hc : ((81841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((246759863033/10000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((81841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c12 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((688709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2027723/10000000) (δ := 439/100000000) (ψ := -1458309/1000000) 80 32
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t12 : ((1987987056909/10000000000000 : ℚ) : ℝ) ≤ stT80 12 := by
  have hc : ((688659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1987987056909/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((688659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c13 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((7707/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215893/1250000) (δ := 91/20000000) (ψ := -1458309/1000000) 80 33
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t13 : ((85495911/400000000 : ℚ) : ℝ) ≤ stT80 13 := by
  have hc : ((15413/20000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85495911/400000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((15413/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c14 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((501551/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2613513/10000000) (δ := 577/100000000) (ψ := -1458309/1000000) 80 34
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t14 : ((335079397653/2500000000000 : ℚ) : ℝ) ≤ stT80 14 := by
  have hc : ((501501/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((335079397653/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((501501/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c15 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-118057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2261451/5000000) (δ := 403/50000000) (ψ := -1458309/1000000) 80 35
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t15 : ((-152443212549/2500000000000 : ℚ) : ℝ) ≤ stT80 15 := by
  have hc : ((-59041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-152443212549/2500000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-59041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c16 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-977543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7323161/10000000) (δ := 159/25000000) (ψ := -1458309/1000000) 80 36
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t16 : ((-2443983477593/10000000000000 : ℚ) : ℝ) ≤ stT80 16 := by
  have hc : ((-977593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).2
  have h0 : (0:ℝ) ≤ ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2443983477593/10000000000000 : ℚ) : ℝ)
      = ((2500001/10000000 : ℚ) : ℝ) * ((-977593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c17 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-85703/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4801763/10000000) (δ := 119/25000000) (ψ := -1458309/1000000) 80 36
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t17 : ((-415781375867/5000000000000 : ℚ) : ℝ) ≤ stT80 17 := by
  have hc : ((-171431/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-415781375867/5000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-171431/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c18 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((977991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 525483/10000000) (δ := 229/50000000) (ψ := -1458309/1000000) 80 37
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t18 : ((1152514225851/5000000000000 : ℚ) : ℝ) ≤ stT80 18 := by
  have hc : ((977941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1152514225851/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((977941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c19 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-87949/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1092259/2500000) (δ := 629/100000000) (ψ := -1458309/1000000) 80 38
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t19 : ((-50456563973/1250000000000 : ℚ) : ℝ) ≤ stT80 19 := by
  have hc : ((-43987/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50456563973/1250000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-43987/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c20 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-706863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5889623/10000000) (δ := 589/100000000) (ψ := -1458309/1000000) 80 38
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t20 : ((-395176384521/2500000000000 : ℚ) : ℝ) ≤ stT80 20 := by
  have hc : ((-706913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-395176384521/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-706913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c21 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((999709/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -15077/2500000) (δ := 523/100000000) (ψ := -1458309/1000000) 80 39
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t21 : ((1090716938651/5000000000000 : ℚ) : ℝ) ≤ stT80 21 := by
  have hc : ((999659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1090716938651/5000000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((999659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c22 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-424717/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1616067/2500000) (δ := 41/10000000) (ψ := -1458309/1000000) 80 40
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t22 : ((-56597083871/312500000000 : ℚ) : ℝ) ≤ stT80 22 := by
  have hc : ((-212371/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56597083871/312500000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-212371/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c23 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((282471/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 606521/2500000) (δ := 713/100000000) (ψ := -1458309/1000000) 80 40
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t23 : ((36808786389/312500000000 : ℚ) : ℝ) ≤ stT80 23 := by
  have hc : ((141223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36808786389/312500000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((141223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c24 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-330833/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1192489/2500000) (δ := 291/50000000) (ψ := -1458309/1000000) 80 41
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t24 : ((-337706138343/5000000000000 : ℚ) : ℝ) ≤ stT80 24 := by
  have hc : ((-330883/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-337706138343/5000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-330883/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c25 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((52853/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3394443/10000000) (δ := 311/50000000) (ψ := -1458309/1000000) 80 41
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t25 : ((105681/2500000 : ℚ) : ℝ) ≤ stT80 25 := by
  have hc : ((105681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105681/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((105681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c26 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-215257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2234689/5000000) (δ := 531/100000000) (ψ := -1458309/1000000) 80 42
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t26 : ((-211125953367/5000000000000 : ℚ) : ℝ) ≤ stT80 26 := by
  have hc : ((-215307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211125953367/5000000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-215307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c27 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((332847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96209/312500) (δ := 2/390625) (ψ := -1458309/1000000) 80 42
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t27 : ((1280935653/20000000000 : ℚ) : ℝ) ≤ stT80 27 := by
  have hc : ((332797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1280935653/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((332797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c28 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-16903/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2677873/5000000) (δ := 721/100000000) (ψ := -1458309/1000000) 80 43
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t28 : ((-511146096279/5000000000000 : ℚ) : ℝ) ≤ stT80 28 := by
  have hc : ((-270473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-511146096279/5000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-270473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c29 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((786913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1662517/10000000) (δ := 601/100000000) (ψ := -1458309/1000000) 80 43
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t29 : ((1461167608439/10000000000000 : ℚ) : ℝ) ≤ stT80 29 := by
  have hc : ((786863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1461167608439/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((786863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c30 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-972389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1453027/2000000) (δ := 653/100000000) (ψ := -1458309/1000000) 80 44
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t30 : ((-887711362369/5000000000000 : ℚ) : ℝ) ≤ stT80 30 := by
  have hc : ((-972439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-887711362369/5000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-972439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c31 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((960259/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -707171/10000000) (δ := 79/10000000) (ψ := -1458309/1000000) 80 44
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t31 : ((1724586255077/10000000000000 : ℚ) : ℝ) ≤ stT80 31 := by
  have hc : ((960209/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1724586255077/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((960209/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c32 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-316813/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5642569/10000000) (δ := 79/10000000) (ψ := -1458309/1000000) 80 44
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t32 : ((-280047880373/2500000000000 : ℚ) : ℝ) ≤ stT80 32 := by
  have hc : ((-158419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).2
  have h0 : (0:ℝ) ≤ ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-280047880373/2500000000000 : ℚ) : ℝ)
      = ((1767767/10000000 : ℚ) : ℝ) * ((-158419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c33 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((6371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3911063/10000000) (δ := 29/6250000) (ψ := -1458309/1000000) 80 45
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t33 : ((1375430637/1250000000000 : ℚ) : ℝ) ≤ stT80 33 := by
  have hc : ((6321/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1375430637/1250000000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((6321/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c34 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((679429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 205953/1000000) (δ := 619/100000000) (ψ := -1458309/1000000) 80 45
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t34 : ((233024958863/2000000000000 : ℚ) : ℝ) ≤ stT80 34 := by
  have hc : ((679379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233024958863/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((679379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c35 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-999999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3925463/5000000) (δ := 19/4000000) (ψ := -1458309/1000000) 80 46
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t35 : ((-1690391825141/10000000000000 : ℚ) : ℝ) ≤ stT80 35 := by
  have hc : ((-1000049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1690391825141/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-1000049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c36 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((631973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2216751/10000000) (δ := 33/6250000) (ψ := -1458309/1000000) 80 46
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t36 : ((526602289359/5000000000000 : ℚ) : ℝ) ≤ stT80 36 := by
  have hc : ((631923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((526602289359/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((631923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c37 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((65617/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 815761/2500000) (δ := 91/12500000) (ψ := -1458309/1000000) 80 46
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t37 : ((215706152701/5000000000000 : ℚ) : ℝ) ≤ stT80 37 := by
  have hc : ((131209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((215706152701/5000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((131209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c38 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-478097/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711127/1000000) (δ := 89/20000000) (ψ := -1458309/1000000) 80 47
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t38 : ((-77561668023/500000000000 : ℚ) : ℝ) ≤ stT80 38 := by
  have hc : ((-239061/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77561668023/500000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-239061/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c39 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((180091/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -479043/2500000) (δ := 219/50000000) (ψ := -1458309/1000000) 80 47
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t39 : ((576712561117/5000000000000 : ℚ) : ℝ) ≤ stT80 39 := by
  have hc : ((360157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((576712561117/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((360157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c40 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((306811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3147389/10000000) (δ := 81/20000000) (ψ := -1458309/1000000) 80 47
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t40 : ((242515737009/5000000000000 : ℚ) : ℝ) ≤ stT80 40 := by
  have hc : ((306761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((242515737009/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((306761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c41 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-9957/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1905513/2500000) (δ := 31/6250000) (ψ := -1458309/1000000) 80 48
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t41 : ((-3110201227/20000000000 : ℚ) : ℝ) ≤ stT80 41 := by
  have hc : ((-3983/4000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3110201227/20000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-3983/4000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c42 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((434767/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2802541/10000000) (δ := 667/100000000) (ψ := -1458309/1000000) 80 48
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t42 : ((670782676661/10000000000000 : ℚ) : ℝ) ≤ stT80 42 := by
  have hc : ((434717/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((670782676661/10000000000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((434717/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c43 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((144771/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 951779/5000000) (δ := 707/100000000) (ψ := -1458309/1000000) 80 48
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t43 : ((44151670717/400000000000 : ℚ) : ℝ) ≤ stT80 43 := by
  have hc : ((144761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44151670717/400000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((144761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c44 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-85719/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3250731/5000000) (δ := 547/100000000) (ψ := -1458309/1000000) 80 48
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t44 : ((-32308454067/250000000000 : ℚ) : ℝ) ≤ stT80 44 := by
  have hc : ((-21431/25000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32308454067/250000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-21431/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c45 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-154421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -471193/1000000) (δ := 707/100000000) (ψ := -1458309/1000000) 80 49
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t45 : ((-14389656597/312500000000 : ℚ) : ℝ) ≤ stT80 45 := by
  have hc : ((-77223/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14389656597/312500000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-77223/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c46 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((198403/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316149/10000000) (δ := 747/100000000) (ψ := -1458309/1000000) 80 49
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t46 : ((292514408667/2000000000000 : ℚ) : ℝ) ≤ stT80 46 := by
  have hc : ((198393/200000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((292514408667/2000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((198393/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c47 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-11619/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 996273/2500000) (δ := 51/6250000) (ψ := -1458309/1000000) 80 49
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t47 : ((-84922603/25000000000 : ℚ) : ℝ) ≤ stT80 47 := by
  have hc : ((-2911/125000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84922603/25000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-2911/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c48 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-990669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7512189/10000000) (δ := 363/50000000) (ψ := -1458309/1000000) 80 50
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t48 : ((-89373751709/625000000000 : ℚ) : ℝ) ≤ stT80 48 := by
  have hc : ((-990719/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89373751709/625000000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-990719/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c49 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((1069/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -847083/2500000) (δ := 757/100000000) (ψ := -1458309/1000000) 80 50
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t49 : ((244285641/8000000000 : ℚ) : ℝ) ≤ stT80 49 := by
  have hc : ((171/800 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((244285641/8000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((171/800 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c50 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((483081/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65221/1000000) (δ := 383/50000000) (ψ := -1458309/1000000) 80 50
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t50 : ((42696504683/312500000000 : ℚ) : ℝ) ≤ stT80 50 := by
  have hc : ((30191/31250 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42696504683/312500000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((30191/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c51 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-270871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 922547/2000000) (δ := 283/50000000) (ψ := -1458309/1000000) 80 50
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t51 : ((-379365528801/10000000000000 : ℚ) : ℝ) ≤ stT80 51 := by
  have hc : ((-270921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379365528801/10000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-270921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c52 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-96717/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7211611/10000000) (δ := 27/4000000) (ψ := -1458309/1000000) 80 51
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t52 : ((-67064665111/500000000000 : ℚ) : ℝ) ≤ stT80 52 := by
  have hc : ((-48361/50000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67064665111/500000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-48361/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c53 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((208467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -850493/2500000) (δ := 143/20000000) (ψ := -1458309/1000000) 80 51
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t53 : ((57256526657/2000000000000 : ℚ) : ℝ) ≤ stT80 53 := by
  have hc : ((208417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57256526657/2000000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((208417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c54 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((495479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 67291/2000000) (δ := 87/20000000) (ψ := -1458309/1000000) 80 51
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t54 : ((337113590229/2500000000000 : ℚ) : ℝ) ≤ stT80 54 := by
  have hc : ((247727/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337113590229/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((247727/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c55 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-31711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2003141/5000000) (δ := 81/12500000) (ψ := -1458309/1000000) 80 51
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t55 : ((-107066331/25000000000 : ℚ) : ℝ) ≤ stT80 55 := by
  have hc : ((-31761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107066331/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-31761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c56 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-995241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7609983/10000000) (δ := 43/6250000) (ψ := -1458309/1000000) 80 51
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t56 : ((-1330014330337/10000000000000 : ℚ) : ℝ) ≤ stT80 56 := by
  have hc : ((-995291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1330014330337/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-995291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c57 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-249757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -284879/625000) (δ := 539/100000000) (ψ := -1458309/1000000) 80 52
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t57 : ((-330877615131/10000000000000 : ℚ) : ℝ) ≤ stT80 57 := by
  have hc : ((-249807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330877615131/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-249807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c58 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((454089/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -269929/2500000) (δ := 93/12500000) (ψ := -1458309/1000000) 80 52
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t58 : ((4657930407/39062500000 : ℚ) : ℝ) ≤ stT80 58 := by
  have hc : ((28379/31250 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4657930407/39062500000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((28379/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c59 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((1854/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2339171/10000000) (δ := 29/6250000) (ψ := -1458309/1000000) 80 52
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t59 : ((77231961147/1000000000000 : ℚ) : ℝ) ≤ stT80 59 := by
  have hc : ((59323/100000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77231961147/1000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((59323/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c60 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-65141/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1140119/2000000) (δ := 499/100000000) (ψ := -1458309/1000000) 80 52
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t60 : ((-8410316027/100000000000 : ℚ) : ℝ) ≤ stT80 60 := by
  have hc : ((-32573/50000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8410316027/100000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-32573/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c61 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-895613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1675377/2500000) (δ := 51/10000000) (ψ := -1458309/1000000) 80 53
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t61 : ((-1146779139647/10000000000000 : ℚ) : ℝ) ≤ stT80 61 := by
  have hc : ((-895663/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).2
  have h0 : (0:ℝ) ≤ ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1146779139647/10000000000000 : ℚ) : ℝ)
      = ((1280369/10000000 : ℚ) : ℝ) * ((-895663/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c62 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((1519/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -862351/2500000) (δ := 67/10000000) (ψ := -1458309/1000000) 80 53
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t62 : ((9643117593/400000000000 : ℚ) : ℝ) ≤ stT80 62 := by
  have hc : ((7593/40000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9643117593/400000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((7593/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c63 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((995031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -31167/1250000) (δ := 613/100000000) (ψ := -1458309/1000000) 80 53
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t63 : ((1253557657261/10000000000000 : ℚ) : ℝ) ≤ stT80 63 := by
  have hc : ((994981/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1253557657261/10000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((994981/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c64 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((399217/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 580067/2000000) (δ := 63/10000000) (ψ := -1458309/1000000) 80 53
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t64 : ((399167/8000000 : ℚ) : ℝ) ≤ stT80 64 := by
  have hc : ((399167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((399167/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((399167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c65 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-737711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6001173/10000000) (δ := 11/2000000) (ψ := -1458309/1000000) 80 53
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t65 : ((-228770095207/2500000000000 : ℚ) : ℝ) ≤ stT80 65 := by
  have hc : ((-737761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-228770095207/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-737761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c66 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-221717/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -415831/625000) (δ := 483/100000000) (ψ := -1458309/1000000) 80 54
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t66 : ((-109172066997/1000000000000 : ℚ) : ℝ) ≤ stT80 66 := by
  have hc : ((-443459/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-109172066997/1000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-443459/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c67 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((112271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3645721/10000000) (δ := 683/100000000) (ψ := -1458309/1000000) 80 54
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t67 : ((68549861187/5000000000000 : ℚ) : ℝ) ≤ stT80 67 := by
  have hc : ((112221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68549861187/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((112221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c68 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((15046/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -682703/10000000) (δ := 763/100000000) (ψ := -1458309/1000000) 80 54
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t68 : ((291920092533/2500000000000 : ℚ) : ℝ) ≤ stT80 68 := by
  have hc : ((481447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291920092533/2500000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((481447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c69 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((625657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 17477/78125) (δ := 803/100000000) (ψ := -1458309/1000000) 80 54
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t69 : ((376570995903/5000000000000 : ℚ) : ℝ) ≤ stT80 69 := by
  have hc : ((625607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((376570995903/5000000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((625607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c70 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-9149/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1278701/2500000) (δ := 483/100000000) (ψ := -1458309/1000000) 80 54
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t70 : ((-218726907/4000000000 : ℚ) : ℝ) ≤ stT80 70 := by
  have hc : ((-183/400 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218726907/4000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-183/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c71 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-249809/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -969529/1250000) (δ := 611/100000000) (ψ := -1458309/1000000) 80 55
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t71 : ((-296483659413/2500000000000 : ℚ) : ℝ) ≤ stT80 71 := by
  have hc : ((-499643/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-296483659413/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-499643/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c72 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-401173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -619873/1250000) (δ := 21/3125000) (ψ := -1458309/1000000) 80 55
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t72 : ((-29552882511/625000000000 : ℚ) : ℝ) ≤ stT80 72 := by
  have hc : ((-401223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29552882511/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-401223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c73 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((159263/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3438/15625) (δ := 2/390625) (ψ := -1458309/1000000) 80 55
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t73 : ((372777073911/5000000000000 : ℚ) : ℝ) ≤ stT80 73 := by
  have hc : ((318501/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372777073911/5000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((318501/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c74 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((978379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 520811/10000000) (δ := 731/100000000) (ψ := -1458309/1000000) 80 55
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t74 : ((284320995651/2500000000000 : ℚ) : ℝ) ≤ stT80 74 := by
  have hc : ((978329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((284320995651/2500000000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((978329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c75 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((284639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 641083/2000000) (δ := 89/12500000) (ψ := -1458309/1000000) 80 55
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t75 : ((3286149183/100000000000 : ℚ) : ℝ) ≤ stT80 75 := by
  have hc : ((284589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3286149183/100000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((284589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c76 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-174211/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 292723/500000) (δ := 2/390625) (ψ := -1458309/1000000) 80 55
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t76 : ((-399696236313/5000000000000 : ℚ) : ℝ) ≤ stT80 76 := by
  have hc : ((-348447/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-399696236313/5000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-348447/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c77 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-193981/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7239087/10000000) (δ := 661/100000000) (ψ := -1458309/1000000) 80 56
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t77 : ((-110536653773/1000000000000 : ℚ) : ℝ) ≤ stT80 77 := by
  have hc : ((-193991/200000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-110536653773/1000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-193991/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c78 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-28841/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2329203/5000000) (δ := 621/100000000) (ψ := -1458309/1000000) 80 56
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t78 : ((-8165422797/250000000000 : ℚ) : ℝ) ≤ stT80 78 := by
  have hc : ((-14423/50000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8165422797/250000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-14423/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c79 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((664299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2110601/10000000) (δ := 421/100000000) (ψ := -1458309/1000000) 80 56
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t79 : ((747337914663/10000000000000 : ℚ) : ℝ) ≤ stT80 79 := by
  have hc : ((664249/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((747337914663/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((664249/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c80 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((986897/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 101289/2500000) (δ := 541/100000000) (ψ := -1458309/1000000) 80 56
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t80 : ((1103327511951/10000000000000 : ℚ) : ℝ) ≤ stT80 80 := by
  have hc : ((986847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1103327511951/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((986847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c81 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((50391/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 144483/500000) (δ := 211/50000000) (ψ := -1458309/1000000) 80 56
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t81 : ((223932199829/5000000000000 : ℚ) : ℝ) ≤ stT80 81 := by
  have hc : ((201539/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((223932199829/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((201539/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c82 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-53683/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2671839/5000000) (δ := 461/100000000) (ψ := -1458309/1000000) 80 56
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t82 : ((-1852766169/31250000000 : ℚ) : ℝ) ≤ stT80 82 := by
  have hc : ((-6711/12500 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1852766169/31250000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-6711/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c83 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-62463/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7767951/10000000) (δ := 741/100000000) (ψ := -1458309/1000000) 80 56
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t83 : ((-548524038747/5000000000000 : ℚ) : ℝ) ≤ stT80 83 := by
  have hc : ((-499729/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-548524038747/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-499729/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c84 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-301443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -221791/400000) (δ := 851/100000000) (ψ := -1458309/1000000) 80 57
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t84 : ((-8223218003/125000000000 : ℚ) : ℝ) ≤ stT80 84 := by
  have hc : ((-75367/125000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8223218003/125000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-75367/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c85 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((295179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3177883/10000000) (δ := 27/6250000) (ψ := -1458309/1000000) 80 57
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t85 : ((80028065027/2500000000000 : ℚ) : ℝ) ≤ stT80 85 := by
  have hc : ((295129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80028065027/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((295129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c86 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((14754/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -33547/400000) (δ := 47/6250000) (ψ := -1458309/1000000) 80 57
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t86 : ((509081411681/5000000000000 : ℚ) : ℝ) ≤ stT80 86 := by
  have hc : ((472103/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((509081411681/5000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((472103/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c87 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((831277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1473489/10000000) (δ := 691/100000000) (ψ := -1458309/1000000) 80 57
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t87 : ((55698027589/625000000000 : ℚ) : ℝ) ≤ stT80 87 := by
  have hc : ((831227/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((55698027589/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((831227/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c88 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((33527/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3759229/10000000) (δ := 691/100000000) (ψ := -1458309/1000000) 80 57
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t88 : ((17856616253/2500000000000 : ℚ) : ℝ) ≤ stT80 88 := by
  have hc : ((16751/250000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17856616253/2500000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((16751/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c89 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-742543/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 300957/500000) (δ := 69/12500000) (ψ := -1458309/1000000) 80 57
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t89 : ((-393573547407/5000000000000 : ℚ) : ℝ) ≤ stT80 89 := by
  have hc : ((-742593/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-393573547407/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-742593/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c90 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-987239/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7454163/10000000) (δ := 563/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t90 : ((-1040694423877/10000000000000 : ℚ) : ℝ) ≤ stT80 90 := by
  have hc : ((-987289/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1040694423877/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-987289/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c91 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-502841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1311049/2500000) (δ := 843/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t91 : ((-105434618387/2000000000000 : ℚ) : ℝ) ≤ stT80 91 := by
  have hc : ((-502891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-105434618387/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-502891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c92 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((68099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1529191/5000000) (δ := 603/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t92 : ((17746921227/500000000000 : ℚ) : ℝ) ≤ stT80 92 := by
  have hc : ((68089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17746921227/500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((68089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c93 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((936431/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -896199/10000000) (δ := 723/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t93 : ((970981214331/10000000000000 : ℚ) : ℝ) ≤ stT80 93 := by
  have hc : ((936381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((970981214331/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((936381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c94 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((219737/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1242859/10000000) (δ := 643/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t94 : ((453256927029/5000000000000 : ℚ) : ℝ) ≤ stT80 94 := by
  have hc : ((439449/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453256927029/5000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((439449/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c95 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((225137/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3359281/10000000) (δ := 723/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t95 : ((115467155043/5000000000000 : ℚ) : ℝ) ≤ stT80 95 := by
  have hc : ((225087/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((115467155043/5000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((225087/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c96 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-8959/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5453541/10000000) (δ := 723/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t96 : ((-292625308773/5000000000000 : ℚ) : ℝ) ≤ stT80 96 := by
  have hc : ((-286713/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-292625308773/5000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-286713/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c97 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-247853/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3763049/5000000) (δ := 603/100000000) (ψ := -1458309/1000000) 80 58
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t97 : ((-503338983657/5000000000000 : ℚ) : ℝ) ≤ stT80 97 := by
  have hc : ((-495731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503338983657/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-495731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c98 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-771649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1226113/2000000) (δ := 307/50000000) (ψ := -1458309/1000000) 80 59
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t98 : ((-779534059947/10000000000000 : ℚ) : ℝ) ≤ stT80 98 := by
  have hc : ((-771699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-779534059947/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-771699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c99 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((-13837/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4100091/10000000) (δ := 429/100000000) (ψ := -1458309/1000000) 80 59
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t99 : ((-6958380593/1000000000000 : ℚ) : ℝ) ≤ stT80 99 := by
  have hc : ((-13847/200000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6958380593/1000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-13847/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_c100 :
    |Real.cos (((80 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ))
      - ((670429/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -261253/1250000) (δ := 327/50000000) (ψ := -1458309/1000000) 80 59
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st80_t100 : ((670378329621/10000000000000 : ℚ) : ℝ) ≤ stT80 100 := by
  have hc : ((670379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((80 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-1458309/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st80_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((670378329621/10000000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((670379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st80_p1 : ((561/5000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT80 (i+1) := by
  rw [Finset.sum_range_one]
  exact st80_t1

theorem st80_p2 : ((7735901305249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT80 (i+1))
      = (∑ i ∈ Finset.range 1, stT80 (i+1)) + stT80 2 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 1
    simpa using h
  have hprev := st80_p1
  have hstep := st80_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p3 : ((8815205542631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT80 (i+1))
      = (∑ i ∈ Finset.range 2, stT80 (i+1)) + stT80 3 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 2
    simpa using h
  have hprev := st80_p2
  have hstep := st80_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p4 : ((12522505542631/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT80 (i+1))
      = (∑ i ∈ Finset.range 3, stT80 (i+1)) + stT80 4 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 3
    simpa using h
  have hprev := st80_p3
  have hstep := st80_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p5 : ((2359526981387/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT80 (i+1))
      = (∑ i ∈ Finset.range 4, stT80 (i+1)) + stT80 5 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 4
    simpa using h
  have hprev := st80_p4
  have hstep := st80_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p6 : ((3142861380101/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT80 (i+1))
      = (∑ i ∈ Finset.range 5, stT80 (i+1)) + stT80 6 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 5
    simpa using h
  have hprev := st80_p5
  have hstep := st80_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p7 : ((3897750778001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT80 (i+1))
      = (∑ i ∈ Finset.range 6, stT80 (i+1)) + stT80 7 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 6
    simpa using h
  have hprev := st80_p6
  have hstep := st80_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p8 : ((18574280949837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT80 (i+1))
      = (∑ i ∈ Finset.range 7, stT80 (i+1)) + stT80 8 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 7
    simpa using h
  have hprev := st80_p7
  have hstep := st80_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p9 : ((19442994196299/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT80 (i+1))
      = (∑ i ∈ Finset.range 8, stT80 (i+1)) + stT80 9 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 8
    simpa using h
  have hprev := st80_p8
  have hstep := st80_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p10 : ((16432404347403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT80 (i+1))
      = (∑ i ∈ Finset.range 9, stT80 (i+1)) + stT80 10 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 9
    simpa using h
  have hprev := st80_p9
  have hstep := st80_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p11 : ((4169791052609/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT80 (i+1))
      = (∑ i ∈ Finset.range 10, stT80 (i+1)) + stT80 11 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 10
    simpa using h
  have hprev := st80_p10
  have hstep := st80_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p12 : ((3733430253469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT80 (i+1))
      = (∑ i ∈ Finset.range 11, stT80 (i+1)) + stT80 12 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 11
    simpa using h
  have hprev := st80_p11
  have hstep := st80_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p13 : ((4160909808469/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT80 (i+1))
      = (∑ i ∈ Finset.range 12, stT80 (i+1)) + stT80 13 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 12
    simpa using h
  have hprev := st80_p12
  have hstep := st80_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p14 : ((22144866632957/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT80 (i+1))
      = (∑ i ∈ Finset.range 13, stT80 (i+1)) + stT80 14 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 13
    simpa using h
  have hprev := st80_p13
  have hstep := st80_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p15 : ((21535093782761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT80 (i+1))
      = (∑ i ∈ Finset.range 14, stT80 (i+1)) + stT80 15 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 14
    simpa using h
  have hprev := st80_p14
  have hstep := st80_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p16 : ((1193194394073/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT80 (i+1))
      = (∑ i ∈ Finset.range 15, stT80 (i+1)) + stT80 16 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 15
    simpa using h
  have hprev := st80_p15
  have hstep := st80_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p17 : ((9129773776717/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT80 (i+1))
      = (∑ i ∈ Finset.range 16, stT80 (i+1)) + stT80 17 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 16
    simpa using h
  have hprev := st80_p16
  have hstep := st80_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p18 : ((1285286000321/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT80 (i+1))
      = (∑ i ∈ Finset.range 17, stT80 (i+1)) + stT80 18 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 17
    simpa using h
  have hprev := st80_p17
  have hstep := st80_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p19 : ((2520115436669/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT80 (i+1))
      = (∑ i ∈ Finset.range 18, stT80 (i+1)) + stT80 19 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 18
    simpa using h
  have hprev := st80_p18
  have hstep := st80_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p20 : ((4645054488817/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT80 (i+1))
      = (∑ i ∈ Finset.range 19, stT80 (i+1)) + stT80 20 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 19
    simpa using h
  have hprev := st80_p19
  have hstep := st80_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p21 : ((2076165183257/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT80 (i+1))
      = (∑ i ∈ Finset.range 20, stT80 (i+1)) + stT80 21 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 20
    simpa using h
  have hprev := st80_p20
  have hstep := st80_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p22 : ((9475272574349/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT80 (i+1))
      = (∑ i ∈ Finset.range 21, stT80 (i+1)) + stT80 22 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 21
    simpa using h
  have hprev := st80_p21
  have hstep := st80_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p23 : ((10064213156573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT80 (i+1))
      = (∑ i ∈ Finset.range 22, stT80 (i+1)) + stT80 23 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 22
    simpa using h
  have hprev := st80_p22
  have hstep := st80_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p24 : ((972650701823/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT80 (i+1))
      = (∑ i ∈ Finset.range 23, stT80 (i+1)) + stT80 24 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 23
    simpa using h
  have hprev := st80_p23
  have hstep := st80_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p25 : ((993786901823/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT80 (i+1))
      = (∑ i ∈ Finset.range 24, stT80 (i+1)) + stT80 25 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 24
    simpa using h
  have hprev := st80_p24
  have hstep := st80_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p26 : ((9726743064863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT80 (i+1))
      = (∑ i ∈ Finset.range 25, stT80 (i+1)) + stT80 26 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 25
    simpa using h
  have hprev := st80_p25
  have hstep := st80_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p27 : ((10046976978113/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT80 (i+1))
      = (∑ i ∈ Finset.range 26, stT80 (i+1)) + stT80 27 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 26
    simpa using h
  have hprev := st80_p26
  have hstep := st80_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p28 : ((4767915440917/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT80 (i+1))
      = (∑ i ∈ Finset.range 27, stT80 (i+1)) + stT80 28 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 27
    simpa using h
  have hprev := st80_p27
  have hstep := st80_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p29 : ((20532829372107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT80 (i+1))
      = (∑ i ∈ Finset.range 28, stT80 (i+1)) + stT80 29 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 28
    simpa using h
  have hprev := st80_p28
  have hstep := st80_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p30 : ((18757406647369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT80 (i+1))
      = (∑ i ∈ Finset.range 29, stT80 (i+1)) + stT80 30 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 29
    simpa using h
  have hprev := st80_p29
  have hstep := st80_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p31 : ((10240996451223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT80 (i+1))
      = (∑ i ∈ Finset.range 30, stT80 (i+1)) + stT80 31 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 30
    simpa using h
  have hprev := st80_p30
  have hstep := st80_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p32 : ((9680900690477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT80 (i+1))
      = (∑ i ∈ Finset.range 31, stT80 (i+1)) + stT80 32 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 31
    simpa using h
  have hprev := st80_p31
  have hstep := st80_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p33 : ((387456096521/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT80 (i+1))
      = (∑ i ∈ Finset.range 32, stT80 (i+1)) + stT80 33 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 32
    simpa using h
  have hprev := st80_p32
  have hstep := st80_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p34 : ((4107585924073/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT80 (i+1))
      = (∑ i ∈ Finset.range 33, stT80 (i+1)) + stT80 34 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 33
    simpa using h
  have hprev := st80_p33
  have hstep := st80_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p35 : ((2355942224403/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT80 (i+1))
      = (∑ i ∈ Finset.range 34, stT80 (i+1)) + stT80 35 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 34
    simpa using h
  have hprev := st80_p34
  have hstep := st80_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p36 : ((9950371186971/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT80 (i+1))
      = (∑ i ∈ Finset.range 35, stT80 (i+1)) + stT80 36 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 35
    simpa using h
  have hprev := st80_p35
  have hstep := st80_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p37 : ((1270759667459/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT80 (i+1))
      = (∑ i ∈ Finset.range 36, stT80 (i+1)) + stT80 37 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 36
    simpa using h
  have hprev := st80_p36
  have hstep := st80_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p38 : ((4695230329721/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT80 (i+1))
      = (∑ i ∈ Finset.range 37, stT80 (i+1)) + stT80 38 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 37
    simpa using h
  have hprev := st80_p37
  have hstep := st80_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p39 : ((9967173220559/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT80 (i+1))
      = (∑ i ∈ Finset.range 38, stT80 (i+1)) + stT80 39 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 38
    simpa using h
  have hprev := st80_p38
  have hstep := st80_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p40 : ((79763194981/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT80 (i+1))
      = (∑ i ∈ Finset.range 39, stT80 (i+1)) + stT80 40 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 39
    simpa using h
  have hprev := st80_p39
  have hstep := st80_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p41 : ((4716069325409/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT80 (i+1))
      = (∑ i ∈ Finset.range 40, stT80 (i+1)) + stT80 41 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 40
    simpa using h
  have hprev := st80_p40
  have hstep := st80_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p42 : ((19535059978297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT80 (i+1))
      = (∑ i ∈ Finset.range 41, stT80 (i+1)) + stT80 42 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 41
    simpa using h
  have hprev := st80_p41
  have hstep := st80_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p43 : ((10319425873111/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT80 (i+1))
      = (∑ i ∈ Finset.range 42, stT80 (i+1)) + stT80 43 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 42
    simpa using h
  have hprev := st80_p42
  have hstep := st80_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p44 : ((9673256791771/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT80 (i+1))
      = (∑ i ∈ Finset.range 43, stT80 (i+1)) + stT80 44 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 43
    simpa using h
  have hprev := st80_p43
  have hstep := st80_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p45 : ((9443022286219/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT80 (i+1))
      = (∑ i ∈ Finset.range 44, stT80 (i+1)) + stT80 45 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 44
    simpa using h
  have hprev := st80_p44
  have hstep := st80_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p46 : ((20348616615773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT80 (i+1))
      = (∑ i ∈ Finset.range 45, stT80 (i+1)) + stT80 46 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 45
    simpa using h
  have hprev := st80_p45
  have hstep := st80_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p47 : ((20314647574573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT80 (i+1))
      = (∑ i ∈ Finset.range 46, stT80 (i+1)) + stT80 47 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 46
    simpa using h
  have hprev := st80_p46
  have hstep := st80_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p48 : ((18884667547229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT80 (i+1))
      = (∑ i ∈ Finset.range 47, stT80 (i+1)) + stT80 48 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 47
    simpa using h
  have hprev := st80_p47
  have hstep := st80_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p49 : ((19190024598479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT80 (i+1))
      = (∑ i ∈ Finset.range 48, stT80 (i+1)) + stT80 49 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 48
    simpa using h
  have hprev := st80_p48
  have hstep := st80_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p50 : ((4111262549667/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT80 (i+1))
      = (∑ i ∈ Finset.range 49, stT80 (i+1)) + stT80 50 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 49
    simpa using h
  have hprev := st80_p49
  have hstep := st80_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p51 : ((10088473609767/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT80 (i+1))
      = (∑ i ∈ Finset.range 50, stT80 (i+1)) + stT80 51 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 50
    simpa using h
  have hprev := st80_p50
  have hstep := st80_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p52 : ((9417826958657/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT80 (i+1))
      = (∑ i ∈ Finset.range 51, stT80 (i+1)) + stT80 52 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 51
    simpa using h
  have hprev := st80_p51
  have hstep := st80_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p53 : ((19121936550599/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT80 (i+1))
      = (∑ i ∈ Finset.range 52, stT80 (i+1)) + stT80 53 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 52
    simpa using h
  have hprev := st80_p52
  have hstep := st80_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p54 : ((4094078182303/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT80 (i+1))
      = (∑ i ∈ Finset.range 53, stT80 (i+1)) + stT80 54 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 53
    simpa using h
  have hprev := st80_p53
  have hstep := st80_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p55 : ((4085512875823/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT80 (i+1))
      = (∑ i ∈ Finset.range 54, stT80 (i+1)) + stT80 55 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 54
    simpa using h
  have hprev := st80_p54
  have hstep := st80_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p56 : ((9548775024389/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT80 (i+1))
      = (∑ i ∈ Finset.range 55, stT80 (i+1)) + stT80 56 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 55
    simpa using h
  have hprev := st80_p55
  have hstep := st80_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p57 : ((18766672433647/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT80 (i+1))
      = (∑ i ∈ Finset.range 56, stT80 (i+1)) + stT80 57 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 56
    simpa using h
  have hprev := st80_p56
  have hstep := st80_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p58 : ((19959102617839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT80 (i+1))
      = (∑ i ∈ Finset.range 57, stT80 (i+1)) + stT80 58 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 57
    simpa using h
  have hprev := st80_p57
  have hstep := st80_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p59 : ((20731422229309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT80 (i+1))
      = (∑ i ∈ Finset.range 58, stT80 (i+1)) + stT80 59 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 58
    simpa using h
  have hprev := st80_p58
  have hstep := st80_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p60 : ((19890390626609/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT80 (i+1))
      = (∑ i ∈ Finset.range 59, stT80 (i+1)) + stT80 60 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 59
    simpa using h
  have hprev := st80_p59
  have hstep := st80_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p61 : ((9371805743481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT80 (i+1))
      = (∑ i ∈ Finset.range 60, stT80 (i+1)) + stT80 61 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 60
    simpa using h
  have hprev := st80_p60
  have hstep := st80_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p62 : ((18984689426787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT80 (i+1))
      = (∑ i ∈ Finset.range 61, stT80 (i+1)) + stT80 62 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 61
    simpa using h
  have hprev := st80_p61
  have hstep := st80_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p63 : ((1264890442753/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT80 (i+1))
      = (∑ i ∈ Finset.range 62, stT80 (i+1)) + stT80 63 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 62
    simpa using h
  have hprev := st80_p62
  have hstep := st80_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p64 : ((324018841157/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT80 (i+1))
      = (∑ i ∈ Finset.range 63, stT80 (i+1)) + stT80 64 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 63
    simpa using h
  have hprev := st80_p63
  have hstep := st80_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p65 : ((991106272661/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT80 (i+1))
      = (∑ i ∈ Finset.range 64, stT80 (i+1)) + stT80 65 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 64
    simpa using h
  have hprev := st80_p64
  have hstep := st80_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p66 : ((74921619133/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT80 (i+1))
      = (∑ i ∈ Finset.range 65, stT80 (i+1)) + stT80 66 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 65
    simpa using h
  have hprev := st80_p65
  have hstep := st80_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p67 : ((2358438063203/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT80 (i+1))
      = (∑ i ∈ Finset.range 66, stT80 (i+1)) + stT80 67 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 66
    simpa using h
  have hprev := st80_p66
  have hstep := st80_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p68 : ((5008796218939/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT80 (i+1))
      = (∑ i ∈ Finset.range 67, stT80 (i+1)) + stT80 68 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 67
    simpa using h
  have hprev := st80_p67
  have hstep := st80_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p69 : ((10394163433781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT80 (i+1))
      = (∑ i ∈ Finset.range 68, stT80 (i+1)) + stT80 69 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 68
    simpa using h
  have hprev := st80_p68
  have hstep := st80_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p70 : ((10120754800031/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT80 (i+1))
      = (∑ i ∈ Finset.range 69, stT80 (i+1)) + stT80 70 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 69
    simpa using h
  have hprev := st80_p69
  have hstep := st80_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p71 : ((1905557496241/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT80 (i+1))
      = (∑ i ∈ Finset.range 70, stT80 (i+1)) + stT80 71 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 70
    simpa using h
  have hprev := st80_p70
  have hstep := st80_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p72 : ((9291364421117/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT80 (i+1))
      = (∑ i ∈ Finset.range 71, stT80 (i+1)) + stT80 72 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 71
    simpa using h
  have hprev := st80_p71
  have hstep := st80_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p73 : ((2416035373757/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT80 (i+1))
      = (∑ i ∈ Finset.range 72, stT80 (i+1)) + stT80 73 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 72
    simpa using h
  have hprev := st80_p72
  have hstep := st80_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p74 : ((1023278348633/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT80 (i+1))
      = (∑ i ∈ Finset.range 73, stT80 (i+1)) + stT80 74 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 73
    simpa using h
  have hprev := st80_p73
  have hstep := st80_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p75 : ((259927273637/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT80 (i+1))
      = (∑ i ∈ Finset.range 74, stT80 (i+1)) + stT80 75 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 74
    simpa using h
  have hprev := st80_p74
  have hstep := st80_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p76 : ((9997394709167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT80 (i+1))
      = (∑ i ∈ Finset.range 75, stT80 (i+1)) + stT80 76 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 75
    simpa using h
  have hprev := st80_p75
  have hstep := st80_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p77 : ((4722355720151/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT80 (i+1))
      = (∑ i ∈ Finset.range 76, stT80 (i+1)) + stT80 77 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 76
    simpa using h
  have hprev := st80_p76
  have hstep := st80_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p78 : ((4640701492181/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT80 (i+1))
      = (∑ i ∈ Finset.range 77, stT80 (i+1)) + stT80 78 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 77
    simpa using h
  have hprev := st80_p77
  have hstep := st80_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p79 : ((19310143883387/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT80 (i+1))
      = (∑ i ∈ Finset.range 78, stT80 (i+1)) + stT80 79 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 78
    simpa using h
  have hprev := st80_p78
  have hstep := st80_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p80 : ((10206735697669/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT80 (i+1))
      = (∑ i ∈ Finset.range 79, stT80 (i+1)) + stT80 80 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 79
    simpa using h
  have hprev := st80_p79
  have hstep := st80_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p81 : ((5215333948749/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT80 (i+1))
      = (∑ i ∈ Finset.range 80, stT80 (i+1)) + stT80 81 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 80
    simpa using h
  have hprev := st80_p80
  have hstep := st80_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p82 : ((5067112655229/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT80 (i+1))
      = (∑ i ∈ Finset.range 81, stT80 (i+1)) + stT80 82 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 81
    simpa using h
  have hprev := st80_p81
  have hstep := st80_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p83 : ((9585701271711/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT80 (i+1))
      = (∑ i ∈ Finset.range 82, stT80 (i+1)) + stT80 83 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 82
    simpa using h
  have hprev := st80_p82
  have hstep := st80_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p84 : ((9256772551591/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT80 (i+1))
      = (∑ i ∈ Finset.range 83, stT80 (i+1)) + stT80 84 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 83
    simpa using h
  have hprev := st80_p83
  have hstep := st80_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p85 : ((1883365736329/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT80 (i+1))
      = (∑ i ∈ Finset.range 84, stT80 (i+1)) + stT80 85 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 84
    simpa using h
  have hprev := st80_p84
  have hstep := st80_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p86 : ((4962955046663/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT80 (i+1))
      = (∑ i ∈ Finset.range 85, stT80 (i+1)) + stT80 86 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 85
    simpa using h
  have hprev := st80_p85
  have hstep := st80_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p87 : ((5185747157019/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT80 (i+1))
      = (∑ i ∈ Finset.range 86, stT80 (i+1)) + stT80 87 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 86
    simpa using h
  have hprev := st80_p86
  have hstep := st80_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p88 : ((650450471659/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT80 (i+1))
      = (∑ i ∈ Finset.range 87, stT80 (i+1)) + stT80 88 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 87
    simpa using h
  have hprev := st80_p87
  have hstep := st80_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p89 : ((10013633999137/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT80 (i+1))
      = (∑ i ∈ Finset.range 88, stT80 (i+1)) + stT80 89 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 88
    simpa using h
  have hprev := st80_p88
  have hstep := st80_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p90 : ((18986573574397/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT80 (i+1))
      = (∑ i ∈ Finset.range 89, stT80 (i+1)) + stT80 90 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 89
    simpa using h
  have hprev := st80_p89
  have hstep := st80_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p91 : ((9229700241231/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT80 (i+1))
      = (∑ i ∈ Finset.range 90, stT80 (i+1)) + stT80 91 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 90
    simpa using h
  have hprev := st80_p90
  have hstep := st80_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p92 : ((9407169453501/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT80 (i+1))
      = (∑ i ∈ Finset.range 91, stT80 (i+1)) + stT80 92 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 91
    simpa using h
  have hprev := st80_p91
  have hstep := st80_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p93 : ((19785320121333/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT80 (i+1))
      = (∑ i ∈ Finset.range 92, stT80 (i+1)) + stT80 93 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 92
    simpa using h
  have hprev := st80_p92
  have hstep := st80_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p94 : ((20691833975391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT80 (i+1))
      = (∑ i ∈ Finset.range 93, stT80 (i+1)) + stT80 94 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 93
    simpa using h
  have hprev := st80_p93
  have hstep := st80_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p95 : ((20922768285477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT80 (i+1))
      = (∑ i ∈ Finset.range 94, stT80 (i+1)) + stT80 95 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 94
    simpa using h
  have hprev := st80_p94
  have hstep := st80_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p96 : ((20337517667931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT80 (i+1))
      = (∑ i ∈ Finset.range 95, stT80 (i+1)) + stT80 96 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 95
    simpa using h
  have hprev := st80_p95
  have hstep := st80_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p97 : ((19330839700617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT80 (i+1))
      = (∑ i ∈ Finset.range 96, stT80 (i+1)) + stT80 97 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 96
    simpa using h
  have hprev := st80_p96
  have hstep := st80_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p98 : ((1855130564067/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT80 (i+1))
      = (∑ i ∈ Finset.range 97, stT80 (i+1)) + stT80 98 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 97
    simpa using h
  have hprev := st80_p97
  have hstep := st80_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p99 : ((924086091737/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT80 (i+1))
      = (∑ i ∈ Finset.range 98, stT80 (i+1)) + stT80 99 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 98
    simpa using h
  have hprev := st80_p98
  have hstep := st80_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st80_p100 : ((19152100164361/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT80 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT80 (i+1))
      = (∑ i ∈ Finset.range 99, stT80 (i+1)) + stT80 100 := by
    have h := Finset.sum_range_succ (fun i => stT80 (i+1)) 99
    simpa using h
  have hprev := st80_p99
  have hstep := st80_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 80`.** -/
theorem station_80_sign : 0 < hardyG (((80:ℕ)):ℝ) := by
  have hcore := phase_station_lower 80 100 (by norm_num) (by norm_num)
    ((-1458309/1000000 : ℚ) : ℝ)
  have hchain := st80_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT80 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((80:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-1458309/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((80:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((80:ℕ)):ℝ)+1) * ((((80:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((294721/400000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((19152100164361/10000000000000 : ℚ) : ℝ) - ((294721/400000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-1458309/1000000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((80:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-1458309/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((80:ℕ)):ℝ))).re
      - Real.sin ((-1458309/1000000 : ℚ) : ℝ)
        * (riemannZeta (line (((80:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ)) (T := (((80:ℕ)):ℝ))
    (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((80:ℕ)):ℝ)
      = ((((80:ℕ)):ℝ) * (Real.log (((80:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((80:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_80
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
  have hθwin : |(((-1458309/1000000 : ℚ) : ℝ) + ((10:ℤ)) * (2*Real.pi)) - theta (((80:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((80:ℕ)):ℝ))
    (φ := ((-1458309/1000000 : ℚ) : ℝ) + ((10:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-1458309/1000000 : ℚ)) : ℝ) 10).1,
    (cos_sin_shift (((-1458309/1000000 : ℚ)) : ℝ) 10).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_80_sign
end AxiomAudit
