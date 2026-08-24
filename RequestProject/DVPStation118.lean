import RequestProject.DVPSqrtTable
import RequestProject.DVPLog200Table

/-!
# Station `t = 118` of the extended Hardy ladder (rung-126)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT118 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((118 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((136447/250000 : ℚ) : ℝ))

theorem st118_c1 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((427359/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1364471/10000000) (δ := 41/100000000) (ψ := 136447/250000) 118 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t1 : ((213667/250000 : ℚ) : ℝ) ≤ stT118 1 := by
  have hc : ((213667/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213667/250000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((213667/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c2 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((22663/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43583/400000) (δ := 921/100000000) (ψ := 136447/250000) 118 13
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t2 : ((640971010349/1000000000000 : ℚ) : ℝ) ≤ stT118 2 := by
  have hc : ((90647/100000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((640971010349/1000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((90647/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c3 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-14994/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3570537/5000000) (δ := 1027/100000000) (ψ := 136447/250000) 118 21
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t3 : ((-2770317264999/5000000000000 : ℚ) : ℝ) ≤ stT118 3 := by
  have hc : ((-479833/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2770317264999/5000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-479833/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c4 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((236843/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -814679/10000000) (δ := 7/1000000) (ψ := 136447/250000) 118 26
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t4 : ((473661/1000000 : ℚ) : ℝ) ≤ stT118 4 := by
  have hc : ((473661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((473661/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((473661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c5 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((643047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 136301/625000) (δ := 13/1250000) (ψ := 136447/250000) 118 30
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t5 : ((575113877719/2000000000000 : ℚ) : ℝ) ≤ stT118 5 := by
  have hc : ((642997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((575113877719/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((642997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c6 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-18459/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3433089/5000000) (δ := 403/50000000) (ψ := 136447/250000) 118 34
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t6 : ((-3768131809/10000000000 : ℚ) : ℝ) ≤ stT118 6 := by
  have hc : ((-923/1000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3768131809/10000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-923/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c7 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-965183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3596173/5000000) (δ := 77/12500000) (ψ := 136447/250000) 118 36
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t7 : ((-729647616457/2000000000000 : ℚ) : ℝ) ≤ stT118 7 := by
  have hc : ((-965233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729647616457/2000000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-965233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c8 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((976781/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -539783/10000000) (δ := 703/100000000) (ψ := 136447/250000) 118 39
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t8 : ((3453264682623/10000000000000 : ℚ) : ℝ) ≤ stT118 8 := by
  have hc : ((976731/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3453264682623/10000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((976731/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c9 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((439177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1395143/5000000) (δ := 901/100000000) (ψ := 136447/250000) 118 41
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t9 : ((1463756520291/10000000000000 : ℚ) : ℝ) ≤ stT118 9 := by
  have hc : ((439127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1463756520291/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((439127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c10 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((138781/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2455711/10000000) (δ := 531/50000000) (ψ := 136447/250000) 118 43
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t10 : ((877648871749/5000000000000 : ℚ) : ℝ) ≤ stT118 10 := by
  have hc : ((277537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((877648871749/5000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((277537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c11 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((94359/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13183/156250) (δ := 211/25000000) (ψ := 136447/250000) 118 45
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t11 : ((142243986001/500000000000 : ℚ) : ℝ) ≤ stT118 11 := by
  have hc : ((47177/50000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((142243986001/500000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((47177/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c12 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-13674/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3295641/5000000) (δ := 299/50000000) (ψ := 136447/250000) 118 47
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t12 : ((-39475702123/156250000000 : ℚ) : ℝ) ≤ stT118 12 := by
  have hc : ((-437593/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39475702123/156250000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-437593/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c13 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((865153/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1313353/10000000) (δ := 41/6250000) (ψ := 136447/250000) 118 48
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t13 : ((4798726341/20000000000 : ℚ) : ℝ) ≤ stT118 13 := by
  have hc : ((865103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4798726341/20000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((865103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c14 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-494029/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3733621/5000000) (δ := 209/25000000) (ψ := 136447/250000) 118 49
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t14 : ((-660207571551/2500000000000 : ℚ) : ℝ) ≤ stT118 14 := by
  have hc : ((-247027/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660207571551/2500000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-247027/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c15 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((66047/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -898947/2500000) (δ := 239/20000000) (ψ := 136447/250000) 118 51
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t15 : ((21308501467/625000000000 : ℚ) : ℝ) ≤ stT118 15 := by
  have hc : ((33011/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21308501467/625000000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((33011/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c16 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((124299/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -264887/10000000) (δ := 231/25000000) (ψ := 136447/250000) 118 52
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t16 : ((497171/2000000 : ℚ) : ℝ) ≤ stT118 16 := by
  have hc : ((497171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((497171/2000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((497171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c17 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((721683/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1911413/10000000) (δ := 673/100000000) (ψ := 136447/250000) 118 53
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t17 : ((437554231587/2500000000000 : ℚ) : ℝ) ≤ stT118 17 := by
  have hc : ((721633/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437554231587/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((721633/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c18 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((21121/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1532591/5000000) (δ := 17/2500000) (ψ := 136447/250000) 118 54
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t18 : ((199101183873/2500000000000 : ℚ) : ℝ) ≤ stT118 18 := by
  have hc : ((168943/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199101183873/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((168943/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c19 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((245443/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3307049/10000000) (δ := 931/100000000) (ψ := 136447/250000) 118 55
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t19 : ((562970068701/10000000000000 : ℚ) : ℝ) ≤ stT118 19 := by
  have hc : ((245393/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((562970068701/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((245393/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c20 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((28781/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2730607/10000000) (δ := 421/50000000) (ψ := 136447/250000) 118 56
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t20 : ((514794052941/5000000000000 : ℚ) : ℝ) ≤ stT118 20 := by
  have hc : ((230223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((514794052941/5000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((230223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c21 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((421947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 707871/5000000) (δ := 771/100000000) (ψ := 136447/250000) 118 57
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t21 : ((230177226529/1250000000000 : ℚ) : ℝ) ≤ stT118 21 := by
  have hc : ((210961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230177226529/1250000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((210961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c22 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((974227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35551/625000) (δ := 623/100000000) (ψ := 136447/250000) 118 58
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t22 : ((2076952183239/10000000000000 : ℚ) : ℝ) ≤ stT118 22 := by
  have hc : ((974177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2076952183239/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((974177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c23 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((300667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -316351/1000000) (δ := 1029/100000000) (ψ := 136447/250000) 118 59
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t23 : ((78353716731/1250000000000 : ℚ) : ℝ) ≤ stT118 23 := by
  have hc : ((300617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78353716731/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((300617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c24 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-51047/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6316387/10000000) (δ := 429/50000000) (ψ := 136447/250000) 118 60
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t24 : ((-416822637021/2500000000000 : ℚ) : ℝ) ≤ stT118 24 := by
  have hc : ((-408401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-416822637021/2500000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-408401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c25 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-659117/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2863051/5000000) (δ := 449/50000000) (ψ := 136447/250000) 118 60
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t25 : ((-1318334659167/10000000000000 : ℚ) : ℝ) ≤ stT118 25 := by
  have hc : ((-659167/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1318334659167/10000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-659167/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c26 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((402447/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1588249/10000000) (δ := 187/25000000) (ψ := 136447/250000) 118 61
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t26 : ((394607165971/2500000000000 : ℚ) : ℝ) ≤ stT118 26 := by
  have hc : ((201211/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((394607165971/2500000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((201211/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c27 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((367453/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1493159/5000000) (δ := 373/50000000) (ψ := 136447/250000) 118 62
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t27 : ((1414134147/20000000000 : ℚ) : ℝ) ≤ stT118 27 := by
  have hc : ((367403/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1414134147/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((367403/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c28 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-998999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7742137/10000000) (δ := 1097/100000000) (ψ := 136447/250000) 118 62
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t28 : ((-1888025778327/10000000000000 : ℚ) : ℝ) ≤ stT118 28 := by
  have hc : ((-999049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1888025778327/10000000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-999049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c29 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((289031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2386113/10000000) (δ := 433/50000000) (ψ := 136447/250000) 118 63
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t29 : ((268335279359/2500000000000 : ℚ) : ℝ) ≤ stT118 29 := by
  have hc : ((144503/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((268335279359/2500000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((144503/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c30 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((30009/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -830223/2500000) (δ := 947/100000000) (ψ := 136447/250000) 118 64
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t30 : ((219109003151/5000000000000 : ℚ) : ℝ) ≤ stT118 30 := by
  have hc : ((120011/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((219109003151/5000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((120011/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c31 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-51557/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3176053/5000000) (δ := 71/6250000) (ψ := 136447/250000) 118 64
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t31 : ((-370419074987/2500000000000 : ℚ) : ℝ) ≤ stT118 31 := by
  have hc : ((-412481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-370419074987/2500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-412481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c32 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((124999/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1251/1250000) (δ := 237/20000000) (ψ := 136447/250000) 118 65
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t32 : ((441915867393/2500000000000 : ℚ) : ℝ) ≤ stT118 32 := by
  have hc : ((499971/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441915867393/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((499971/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c33 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-110087/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1655079/2500000) (δ := 689/100000000) (ψ := 136447/250000) 118 66
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t33 : ((-766591189821/5000000000000 : ℚ) : ℝ) ≤ stT118 33 := by
  have hc : ((-440373/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-766591189821/5000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-440373/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c34 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((320681/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2186309/10000000) (δ := 447/50000000) (ψ := 136447/250000) 118 66
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t34 : ((6874002877/62500000000 : ℚ) : ℝ) ≤ stT118 34 := by
  have hc : ((20041/31250 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6874002877/62500000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((20041/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c35 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-405327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4970331/10000000) (δ := 9/1250000) (ψ := 136447/250000) 118 67
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t35 : ((-685212391493/10000000000000 : ℚ) : ℝ) ≤ stT118 35 := by
  have hc : ((-405377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685212391493/10000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-405377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c36 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((46523/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3340077/10000000) (δ := 763/100000000) (ψ := 136447/250000) 118 67
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t36 : ((38760817829/1000000000000 : ℚ) : ℝ) ≤ stT118 36 := by
  have hc : ((46513/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38760817829/1000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((46513/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c37 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-142789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1071297/2500000) (δ := 1033/100000000) (ψ := 136447/250000) 118 68
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t37 : ((-23482588761/1000000000000 : ℚ) : ℝ) ≤ stT118 37 := by
  have hc : ((-142839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23482588761/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-142839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c38 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((137581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 447743/1250000) (δ := 67/10000000) (ψ := 136447/250000) 118 68
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t38 : ((111552356817/5000000000000 : ℚ) : ℝ) ≤ stT118 38 := by
  have hc : ((137531/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111552356817/5000000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((137531/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c39 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-212863/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -17853/40000) (δ := 321/50000000) (ψ := 136447/250000) 118 69
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t39 : ((-170466877233/5000000000000 : ℚ) : ℝ) ≤ stT118 39 := by
  have hc : ((-212913/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170466877233/5000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-212913/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c40 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((72061/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3005503/10000000) (δ := 621/100000000) (ψ := 136447/250000) 118 69
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t40 : ((56961287019/1000000000000 : ℚ) : ℝ) ≤ stT118 40 := by
  have hc : ((72051/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56961287019/1000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((72051/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c41 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-561717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -270907/500000) (δ := 47/6250000) (ψ := 136447/250000) 118 70
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t41 : ((-438666435523/5000000000000 : ℚ) : ℝ) ≤ stT118 41 := by
  have hc : ((-561767/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-438666435523/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-561767/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c42 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((389961/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 845319/5000000) (δ := 991/100000000) (ψ := 136447/250000) 118 70
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t42 : ((37605257243/312500000000 : ℚ) : ℝ) ≤ stT118 42 := by
  have hc : ((24371/31250 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).1
  have hw2 : ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1543033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37605257243/312500000000 : ℚ) : ℝ)
      = ((1543033/10000000 : ℚ) : ℝ) * ((24371/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c43 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-237987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1768957/2500000) (δ := 1001/100000000) (ψ := 136447/250000) 118 71
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t43 : ((-362945905507/2500000000000 : ℚ) : ℝ) ≤ stT118 43 := by
  have hc : ((-475999/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-362945905507/2500000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-475999/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c44 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((993097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293921/10000000) (δ := 821/100000000) (ψ := 136447/250000) 118 71
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t44 : ((374268490783/2500000000000 : ℚ) : ℝ) ≤ stT118 44 := by
  have hc : ((993047/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((374268490783/2500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((993047/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c45 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-164231/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1583893/2500000) (δ := 521/50000000) (ψ := 136447/250000) 118 71
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t45 : ((-30604503699/250000000000 : ℚ) : ℝ) ≤ stT118 45 := by
  have hc : ((-164241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30604503699/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-164241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c46 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((403511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1444307/5000000) (δ := 1113/100000000) (ψ := 136447/250000) 118 72
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t46 : ((594870564159/10000000000000 : ℚ) : ℝ) ≤ stT118 46 := by
  have hc : ((403461/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594870564159/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((403461/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c47 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((37479/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3455717/10000000) (δ := 117/10000000) (ψ := 136447/250000) 118 72
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t47 : ((54654119381/2000000000000 : ℚ) : ℝ) ≤ stT118 47 := by
  have hc : ((37469/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).1
  have hw2 : ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1458649/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54654119381/2000000000000 : ℚ) : ℝ)
      = ((1458649/10000000 : ℚ) : ℝ) * ((37469/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c48 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-374251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6041491/10000000) (δ := 1079/100000000) (ψ := 136447/250000) 118 73
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t48 : ((-8440953059/78125000000 : ℚ) : ℝ) ≤ stT118 48 := by
  have hc : ((-93569/125000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8440953059/78125000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-93569/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c49 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((124983/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41199/10000000) (δ := 143/12500000) (ψ := 136447/250000) 118 73
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t49 : ((714152642897/5000000000000 : ℚ) : ℝ) ≤ stT118 49 := by
  have hc : ((499907/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((714152642897/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((499907/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c50 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-737663/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3000499/5000000) (δ := 1119/100000000) (ψ := 136447/250000) 118 73
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t50 : ((-521642026291/5000000000000 : ℚ) : ℝ) ≤ stT118 50 := by
  have hc : ((-737713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-521642026291/5000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-737713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c51 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((24717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3865191/10000000) (δ := 207/25000000) (ψ := 136447/250000) 118 74
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t51 : ((863517669/250000000000 : ℚ) : ℝ) ≤ stT118 51 := by
  have hc : ((24667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((863517669/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((24667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c52 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((734913/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 372629/2000000) (δ := 121/12500000) (ψ := 136447/250000) 118 74
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t52 : ((4076285061/40000000000 : ℚ) : ℝ) ≤ stT118 52 := by
  have hc : ((734863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4076285061/40000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((734863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c53 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-247243/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3741181/5000000) (δ := 131/12500000) (ψ := 136447/250000) 118 74
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t53 : ((-339631638333/2500000000000 : ℚ) : ℝ) ≤ stT118 53 := by
  have hc : ((-494511/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339631638333/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-494511/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c54 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((233647/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1355711/5000000) (δ := 329/50000000) (ψ := 136447/250000) 118 75
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t54 : ((158959562697/2500000000000 : ℚ) : ℝ) ≤ stT118 54 := by
  have hc : ((116811/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((158959562697/2500000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((116811/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c55 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((470773/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1350787/5000000) (δ := 197/20000000) (ψ := 136447/250000) 118 75
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t55 : ((634722422477/10000000000000 : ℚ) : ℝ) ≤ stT118 55 := by
  have hc : ((470723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((634722422477/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((470723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c56 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-498937/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -769093/1000000) (δ := 33/3125000) (ψ := 136447/250000) 118 76
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t56 : ((-333383206667/2500000000000 : ℚ) : ℝ) ≤ stT118 56 := by
  have hc : ((-249481/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333383206667/2500000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-249481/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c57 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((550509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -493911/2000000) (δ := 97/12500000) (ψ := 136447/250000) 118 76
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t57 : ((182275140047/2500000000000 : ℚ) : ℝ) ≤ stT118 57 := by
  have hc : ((550459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((182275140047/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((550459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c58 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((242513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2661009/10000000) (δ := 1087/100000000) (ψ := 136447/250000) 118 76
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t58 : ((4975035363/78125000000 : ℚ) : ℝ) ≤ stT118 58 := by
  have hc : ((30311/62500 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4975035363/78125000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((30311/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c59 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-499099/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7703867/10000000) (δ := 687/100000000) (ψ := 136447/250000) 118 76
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t59 : ((-16245113609/125000000000 : ℚ) : ℝ) ≤ stT118 59 := by
  have hc : ((-124781/125000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16245113609/125000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-124781/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c60 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((345149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -761499/2500000) (δ := 727/100000000) (ψ := 136447/250000) 118 77
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t60 : ((222760369203/5000000000000 : ℚ) : ℝ) ≤ stT118 60 := by
  have hc : ((345099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).1
  have hw2 : ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((222760369203/5000000000000 : ℚ) : ℝ)
      = ((645497/5000000 : ℚ) : ℝ) * ((345099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c61 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((3719/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 457537/2500000) (δ := 747/100000000) (ψ := 136447/250000) 118 77
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t61 : ((9522737/100000000 : ℚ) : ℝ) ≤ stT118 61 := by
  have hc : ((119/160 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9522737/100000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((119/160 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c62 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-22049/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6627001/10000000) (δ := 967/100000000) (ψ := 136447/250000) 118 77
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t62 : ((-56007723201/500000000000 : ℚ) : ℝ) ≤ stT118 62 := by
  have hc : ((-88201/100000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56007723201/500000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-88201/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c63 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-86339/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4360861/10000000) (δ := 177/20000000) (ψ := 136447/250000) 118 78
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t63 : ((-13601056131/625000000000 : ℚ) : ℝ) ≤ stT118 63 := by
  have hc : ((-21591/125000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13601056131/625000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-21591/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c64 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((993513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35613/1250000) (δ := 479/50000000) (ψ := 136447/250000) 118 78
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t64 : ((993463/8000000 : ℚ) : ℝ) ≤ stT118 64 := by
  have hc : ((993463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((993463/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((993463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c65 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-364093/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4858639/10000000) (δ := 399/50000000) (ψ := 136447/250000) 118 78
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t65 : ((-112916010441/2500000000000 : ℚ) : ℝ) ≤ stT118 65 := by
  have hc : ((-364143/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112916010441/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-364143/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c66 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-823397/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317271/500000) (δ := 143/20000000) (ψ := 136447/250000) 118 79
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t66 : ((-202718652801/2000000000000 : ℚ) : ℝ) ≤ stT118 66 := by
  have hc : ((-823447/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).2
  have h0 : (0:ℝ) ≤ ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-202718652801/2000000000000 : ℚ) : ℝ)
      = ((246183/2000000 : ℚ) : ℝ) * ((-823447/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c67 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((722283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -954623/5000000) (δ := 39/4000000) (ψ := 136447/250000) 118 79
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t67 : ((441173861351/5000000000000 : ℚ) : ℝ) ≤ stT118 67 := by
  have hc : ((722233/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((441173861351/5000000000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((722233/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c68 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((110659/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 615301/2500000) (δ := 231/20000000) (ψ := 136447/250000) 118 79
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t68 : ((67090804011/1000000000000 : ℚ) : ℝ) ≤ stT118 68 := by
  have hc : ((110649/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67090804011/1000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((110649/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c69 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-907101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 135357/200000) (δ := 231/20000000) (ψ := 136447/250000) 118 79
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t69 : ((-1092081895709/10000000000000 : ℚ) : ℝ) ≤ stT118 69 := by
  have hc : ((-907151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1092081895709/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-907151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c70 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-302561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1173859/2500000) (δ := 181/25000000) (ψ := 136447/250000) 118 80
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t70 : ((-361689442919/10000000000000 : ℚ) : ℝ) ≤ stT118 70 := by
  have hc : ((-302611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).2
  have h0 : (0:ℝ) ≤ ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-361689442919/10000000000000 : ℚ) : ℝ)
      = ((1195229/10000000 : ℚ) : ℝ) * ((-302611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c71 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((489593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -63871/1250000) (δ := 899/100000000) (ψ := 136447/250000) 118 80
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t71 : ((18156562519/156250000000 : ℚ) : ℝ) ≤ stT118 71 := by
  have hc : ((15299/15625 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18156562519/156250000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((15299/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c72 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((124483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3614973/10000000) (δ := 123/12500000) (ψ := 136447/250000) 118 80
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t72 : ((146645659263/10000000000000 : ℚ) : ℝ) ≤ stT118 72 := by
  have hc : ((124433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146645659263/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((124433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c73 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-997689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7684003/10000000) (δ := 181/25000000) (ψ := 136447/250000) 118 80
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t73 : ((-291941424617/2500000000000 : ℚ) : ℝ) ≤ stT118 73 := by
  have hc : ((-997739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-291941424617/2500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-997739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c74 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-6663/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4010293/10000000) (δ := 107/10000000) (ψ := 136447/250000) 118 81
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t74 : ((-7757209021/2000000000000 : ℚ) : ℝ) ≤ stT118 74 := by
  have hc : ((-6673/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7757209021/2000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-6673/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c75 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((249949/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25251/5000000) (δ := 1053/100000000) (ψ := 136447/250000) 118 81
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t75 : ((5772033531/50000000000 : ℚ) : ℝ) ≤ stT118 75 := by
  have hc : ((499873/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5772033531/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((499873/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c76 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((28057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96421/250000) (δ := 733/100000000) (ψ := 136447/250000) 118 81
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t76 : ((16063106773/5000000000000 : ℚ) : ℝ) ≤ stT118 76 := by
  have hc : ((28007/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16063106773/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((28007/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c77 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-998413/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 482069/625000) (δ := 953/100000000) (ψ := 136447/250000) 118 81
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t77 : ((-568927212789/5000000000000 : ℚ) : ℝ) ≤ stT118 77 := by
  have hc : ((-998463/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-568927212789/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-998463/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c78 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-20871/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -837671/2000000) (δ := 903/100000000) (ψ := 136447/250000) 118 82
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t78 : ((-11821548459/1000000000000 : ℚ) : ℝ) ≤ stT118 78 := by
  have hc : ((-20881/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).2
  have h0 : (0:ℝ) ≤ ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11821548459/1000000000000 : ℚ) : ℝ)
      = ((566139/5000000 : ℚ) : ℝ) * ((-20881/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c79 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((985221/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -215171/5000000) (δ := 3/500000) (ψ := 136447/250000) 118 82
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t79 : ((1108403084877/10000000000000 : ℚ) : ℝ) ≤ stT118 79 := by
  have hc : ((985171/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1108403084877/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((985171/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c80 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((255763/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3280399/10000000) (δ := 783/100000000) (ψ := 136447/250000) 118 82
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t80 : ((285895572529/10000000000000 : ℚ) : ℝ) ≤ stT118 80 := by
  have hc : ((255713/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).1
  have hw2 : ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1118033/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((285895572529/10000000000000 : ℚ) : ℝ)
      = ((1118033/10000000 : ℚ) : ℝ) * ((255713/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c81 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-934631/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3472521/5000000) (δ := 31/5000000) (ψ := 136447/250000) 118 82
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t81 : ((-129816909409/1250000000000 : ℚ) : ℝ) ≤ stT118 81 := by
  have hc : ((-934681/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-129816909409/1250000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-934681/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c82 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-29221/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1285811/2500000) (δ := 163/25000000) (ψ := 136447/250000) 118 83
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t82 : ((-64545337647/1250000000000 : ℚ) : ℝ) ≤ stT118 82 := by
  have hc : ((-233793/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64545337647/1250000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-233793/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c83 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((161961/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -783721/5000000) (δ := 273/25000000) (ψ := 136447/250000) 118 83
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t83 : ((88882109771/1000000000000 : ℚ) : ℝ) ≤ stT118 83 := by
  have hc : ((161951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((88882109771/1000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((161951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c84 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((70653/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 982767/5000000) (δ := 303/25000000) (ψ := 136447/250000) 118 83
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t84 : ((9635406959/125000000000 : ℚ) : ℝ) ≤ stT118 84 := by
  have hc : ((8831/12500 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9635406959/125000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((8831/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c85 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-57441/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5456699/10000000) (δ := 651/100000000) (ψ := 136447/250000) 118 83
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t85 : ((-31154488119/500000000000 : ℚ) : ℝ) ≤ stT118 85 := by
  have hc : ((-28723/50000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31154488119/500000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-28723/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c86 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-912591/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6800933/10000000) (δ := 551/50000000) (ψ := 136447/250000) 118 84
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t86 : ((-123015793031/1250000000000 : ℚ) : ℝ) ≤ stT118 86 := by
  have hc : ((-912641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-123015793031/1250000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-912641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c87 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((212957/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -339049/1000000) (δ := 981/100000000) (ψ := 136447/250000) 118 84
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t87 : ((14266259349/625000000000 : ℚ) : ℝ) ≤ stT118 87 := by
  have hc : ((212907/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14266259349/625000000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((212907/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c88 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((999971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -761/400000) (δ := 1041/100000000) (ψ := 136447/250000) 118 84
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t88 : ((1065918785763/10000000000000 : ℚ) : ℝ) ≤ stT118 88 := by
  have hc : ((999921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1065918785763/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((999921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c89 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((242613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 414293/1250000) (δ := 401/50000000) (ψ := 136447/250000) 118 84
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t89 : ((257116052311/10000000000000 : ℚ) : ℝ) ≤ stT118 89 := by
  have hc : ((242563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((257116052311/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((242563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c90 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-878823/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1652617/2500000) (δ := 411/50000000) (ψ := 136447/250000) 118 84
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t90 : ((-926413877189/10000000000000 : ℚ) : ℝ) ≤ stT118 90 := by
  have hc : ((-878873/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-926413877189/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-878873/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c91 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-692047/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2918897/5000000) (δ := 1233/100000000) (ψ := 136447/250000) 118 85
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t91 : ((-145102980729/2000000000000 : ℚ) : ℝ) ≤ stT118 91 := by
  have hc : ((-692097/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145102980729/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-692097/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c92 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((12537/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1306859/5000000) (δ := 893/100000000) (ψ := 136447/250000) 118 85
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t92 : ((13069421949/250000000000 : ℚ) : ℝ) ≤ stT118 92 := by
  have hc : ((50143/100000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13069421949/250000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((50143/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c93 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((973621/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 287751/5000000) (δ := 1073/100000000) (ψ := 136447/250000) 118 85
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t93 : ((1009545422021/10000000000000 : ℚ) : ℝ) ≤ stT118 93 := by
  have hc : ((973571/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1009545422021/10000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((973571/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c94 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((78471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 932653/2500000) (δ := 933/100000000) (ψ := 136447/250000) 118 85
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t94 : ((80885066241/10000000000000 : ℚ) : ℝ) ≤ stT118 94 := by
  have hc : ((78421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((80885066241/10000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((78421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c95 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-230201/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1370467/2000000) (δ := 1073/100000000) (ψ := 136447/250000) 118 85
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t95 : ((-472388433033/5000000000000 : ℚ) : ℝ) ≤ stT118 95 := by
  have hc : ((-460427/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-472388433033/5000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-460427/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c96 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-671211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1153319/2000000) (δ := 1063/100000000) (ψ := 136447/250000) 118 86
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t96 : ((-685103073081/10000000000000 : ℚ) : ℝ) ≤ stT118 96 := by
  have hc : ((-671261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-685103073081/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-671261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c97 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((116987/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2709573/10000000) (δ := 903/100000000) (ψ := 136447/250000) 118 86
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t97 : ((118769590677/2500000000000 : ℚ) : ℝ) ≤ stT118 97 := by
  have hc : ((233949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((118769590677/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((233949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c98 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((992017/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 63219/2000000) (δ := 923/100000000) (ψ := 136447/250000) 118 86
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t98 : ((125254681123/1250000000000 : ℚ) : ℝ) ≤ stT118 98 := by
  have hc : ((991967/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125254681123/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((991967/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c99 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((121947/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 827761/2500000) (δ := 31/5000000) (ψ := 136447/250000) 118 86
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t99 : ((61268060557/2500000000000 : ℚ) : ℝ) ≤ stT118 99 := by
  have hc : ((60961/250000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((61268060557/2500000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((60961/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_c100 :
    |Real.cos (((118 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((136447/250000 : ℚ) : ℝ))
      - ((-807299/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6275893/10000000) (δ := 983/100000000) (ψ := 136447/250000) 118 86
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st118_t100 : ((-807349/10000000 : ℚ) : ℝ) ≤ stT118 100 := by
  have hc : ((-807349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((118 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((136447/250000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st118_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-807349/10000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-807349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st118_p1 : ((213667/250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT118 (i+1) := by
  rw [Finset.sum_range_one]
  exact st118_t1

theorem st118_p2 : ((1495639010349/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT118 (i+1))
      = (∑ i ∈ Finset.range 1, stT118 (i+1)) + stT118 2 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 1
    simpa using h
  have hprev := st118_p1
  have hstep := st118_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p3 : ((2353938893373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT118 (i+1))
      = (∑ i ∈ Finset.range 2, stT118 (i+1)) + stT118 3 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 2
    simpa using h
  have hprev := st118_p2
  have hstep := st118_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p4 : ((3538091393373/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT118 (i+1))
      = (∑ i ∈ Finset.range 3, stT118 (i+1)) + stT118 4 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 3
    simpa using h
  have hprev := st118_p3
  have hstep := st118_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p5 : ((17027934962087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT118 (i+1))
      = (∑ i ∈ Finset.range 4, stT118 (i+1)) + stT118 5 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 4
    simpa using h
  have hprev := st118_p4
  have hstep := st118_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p6 : ((13259803153087/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT118 (i+1))
      = (∑ i ∈ Finset.range 5, stT118 (i+1)) + stT118 6 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 5
    simpa using h
  have hprev := st118_p5
  have hstep := st118_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p7 : ((4805782535401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT118 (i+1))
      = (∑ i ∈ Finset.range 6, stT118 (i+1)) + stT118 7 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 6
    simpa using h
  have hprev := st118_p6
  have hstep := st118_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p8 : ((522593190137/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT118 (i+1))
      = (∑ i ∈ Finset.range 7, stT118 (i+1)) + stT118 8 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 7
    simpa using h
  have hprev := st118_p7
  have hstep := st118_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p9 : ((3632146568429/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT118 (i+1))
      = (∑ i ∈ Finset.range 8, stT118 (i+1)) + stT118 9 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 8
    simpa using h
  have hprev := st118_p8
  have hstep := st118_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p10 : ((8141942008607/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT118 (i+1))
      = (∑ i ∈ Finset.range 9, stT118 (i+1)) + stT118 10 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 9
    simpa using h
  have hprev := st118_p9
  have hstep := st118_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p11 : ((9564381868617/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT118 (i+1))
      = (∑ i ∈ Finset.range 10, stT118 (i+1)) + stT118 11 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 10
    simpa using h
  have hprev := st118_p10
  have hstep := st118_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p12 : ((8301159400681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT118 (i+1))
      = (∑ i ∈ Finset.range 11, stT118 (i+1)) + stT118 12 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 11
    simpa using h
  have hprev := st118_p11
  have hstep := st118_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p13 : ((9500840985931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT118 (i+1))
      = (∑ i ∈ Finset.range 12, stT118 (i+1)) + stT118 13 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 12
    simpa using h
  have hprev := st118_p12
  have hstep := st118_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p14 : ((8180425842829/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT118 (i+1))
      = (∑ i ∈ Finset.range 13, stT118 (i+1)) + stT118 14 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 13
    simpa using h
  have hprev := st118_p13
  have hstep := st118_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p15 : ((1670178770913/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT118 (i+1))
      = (∑ i ∈ Finset.range 14, stT118 (i+1)) + stT118 15 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 14
    simpa using h
  have hprev := st118_p14
  have hstep := st118_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p16 : ((1918764270913/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT118 (i+1))
      = (∑ i ∈ Finset.range 15, stT118 (i+1)) + stT118 16 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 15
    simpa using h
  have hprev := st118_p15
  have hstep := st118_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p17 : ((10468929817739/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT118 (i+1))
      = (∑ i ∈ Finset.range 16, stT118 (i+1)) + stT118 17 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 16
    simpa using h
  have hprev := st118_p16
  have hstep := st118_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p18 : ((2173426437097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT118 (i+1))
      = (∑ i ∈ Finset.range 17, stT118 (i+1)) + stT118 18 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 17
    simpa using h
  have hprev := st118_p17
  have hstep := st118_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p19 : ((22297234439671/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT118 (i+1))
      = (∑ i ∈ Finset.range 18, stT118 (i+1)) + stT118 19 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 18
    simpa using h
  have hprev := st118_p18
  have hstep := st118_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p20 : ((23326822545553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT118 (i+1))
      = (∑ i ∈ Finset.range 19, stT118 (i+1)) + stT118 20 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 19
    simpa using h
  have hprev := st118_p19
  have hstep := st118_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p21 : ((5033648071557/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT118 (i+1))
      = (∑ i ∈ Finset.range 20, stT118 (i+1)) + stT118 21 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 20
    simpa using h
  have hprev := st118_p20
  have hstep := st118_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p22 : ((851412266907/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT118 (i+1))
      = (∑ i ∈ Finset.range 21, stT118 (i+1)) + stT118 22 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 21
    simpa using h
  have hprev := st118_p21
  have hstep := st118_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p23 : ((3484002784359/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT118 (i+1))
      = (∑ i ∈ Finset.range 22, stT118 (i+1)) + stT118 23 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 22
    simpa using h
  have hprev := st118_p22
  have hstep := st118_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p24 : ((6551182931697/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT118 (i+1))
      = (∑ i ∈ Finset.range 23, stT118 (i+1)) + stT118 24 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 23
    simpa using h
  have hprev := st118_p23
  have hstep := st118_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p25 : ((24886397067621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT118 (i+1))
      = (∑ i ∈ Finset.range 24, stT118 (i+1)) + stT118 25 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 24
    simpa using h
  have hprev := st118_p24
  have hstep := st118_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p26 : ((5292965146301/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT118 (i+1))
      = (∑ i ∈ Finset.range 25, stT118 (i+1)) + stT118 26 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 25
    simpa using h
  have hprev := st118_p25
  have hstep := st118_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p27 : ((5434378561001/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT118 (i+1))
      = (∑ i ∈ Finset.range 26, stT118 (i+1)) + stT118 27 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 26
    simpa using h
  have hprev := st118_p26
  have hstep := st118_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p28 : ((12641933513339/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT118 (i+1))
      = (∑ i ∈ Finset.range 27, stT118 (i+1)) + stT118 28 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 27
    simpa using h
  have hprev := st118_p27
  have hstep := st118_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p29 : ((13178604072057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT118 (i+1))
      = (∑ i ∈ Finset.range 28, stT118 (i+1)) + stT118 29 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 28
    simpa using h
  have hprev := st118_p28
  have hstep := st118_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p30 : ((1674714134401/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT118 (i+1))
      = (∑ i ∈ Finset.range 29, stT118 (i+1)) + stT118 30 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 29
    simpa using h
  have hprev := st118_p29
  have hstep := st118_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p31 : ((6328437462617/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT118 (i+1))
      = (∑ i ∈ Finset.range 30, stT118 (i+1)) + stT118 31 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 30
    simpa using h
  have hprev := st118_p30
  have hstep := st118_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p32 : ((677035333001/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT118 (i+1))
      = (∑ i ∈ Finset.range 31, stT118 (i+1)) + stT118 32 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 31
    simpa using h
  have hprev := st118_p31
  have hstep := st118_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p33 : ((12774115470199/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT118 (i+1))
      = (∑ i ∈ Finset.range 32, stT118 (i+1)) + stT118 33 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 32
    simpa using h
  have hprev := st118_p32
  have hstep := st118_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p34 : ((13324035700359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT118 (i+1))
      = (∑ i ∈ Finset.range 33, stT118 (i+1)) + stT118 34 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 33
    simpa using h
  have hprev := st118_p33
  have hstep := st118_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p35 : ((1038514360369/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT118 (i+1))
      = (∑ i ∈ Finset.range 34, stT118 (i+1)) + stT118 35 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 34
    simpa using h
  have hprev := st118_p34
  have hstep := st118_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p36 : ((5270093437503/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT118 (i+1))
      = (∑ i ∈ Finset.range 35, stT118 (i+1)) + stT118 36 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 35
    simpa using h
  have hprev := st118_p35
  have hstep := st118_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p37 : ((5223128259981/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT118 (i+1))
      = (∑ i ∈ Finset.range 36, stT118 (i+1)) + stT118 37 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 36
    simpa using h
  have hprev := st118_p36
  have hstep := st118_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p38 : ((26338746013539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT118 (i+1))
      = (∑ i ∈ Finset.range 37, stT118 (i+1)) + stT118 38 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 37
    simpa using h
  have hprev := st118_p37
  have hstep := st118_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p39 : ((25997812259073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT118 (i+1))
      = (∑ i ∈ Finset.range 38, stT118 (i+1)) + stT118 39 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 38
    simpa using h
  have hprev := st118_p38
  have hstep := st118_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p40 : ((26567425129263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT118 (i+1))
      = (∑ i ∈ Finset.range 39, stT118 (i+1)) + stT118 40 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 39
    simpa using h
  have hprev := st118_p39
  have hstep := st118_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p41 : ((25690092258217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT118 (i+1))
      = (∑ i ∈ Finset.range 40, stT118 (i+1)) + stT118 41 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 40
    simpa using h
  have hprev := st118_p40
  have hstep := st118_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p42 : ((26893460489993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT118 (i+1))
      = (∑ i ∈ Finset.range 41, stT118 (i+1)) + stT118 42 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 41
    simpa using h
  have hprev := st118_p41
  have hstep := st118_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p43 : ((5088335373593/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT118 (i+1))
      = (∑ i ∈ Finset.range 42, stT118 (i+1)) + stT118 43 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 42
    simpa using h
  have hprev := st118_p42
  have hstep := st118_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p44 : ((26938750831097/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT118 (i+1))
      = (∑ i ∈ Finset.range 43, stT118 (i+1)) + stT118 44 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 43
    simpa using h
  have hprev := st118_p43
  have hstep := st118_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p45 : ((25714570683137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT118 (i+1))
      = (∑ i ∈ Finset.range 44, stT118 (i+1)) + stT118 45 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 44
    simpa using h
  have hprev := st118_p44
  have hstep := st118_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p46 : ((411085019489/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT118 (i+1))
      = (∑ i ∈ Finset.range 45, stT118 (i+1)) + stT118 46 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 45
    simpa using h
  have hprev := st118_p45
  have hstep := st118_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p47 : ((26582711844201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT118 (i+1))
      = (∑ i ∈ Finset.range 46, stT118 (i+1)) + stT118 47 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 46
    simpa using h
  have hprev := st118_p46
  have hstep := st118_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p48 : ((25502269852649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT118 (i+1))
      = (∑ i ∈ Finset.range 47, stT118 (i+1)) + stT118 48 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 47
    simpa using h
  have hprev := st118_p47
  have hstep := st118_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p49 : ((26930575138443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT118 (i+1))
      = (∑ i ∈ Finset.range 48, stT118 (i+1)) + stT118 49 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 48
    simpa using h
  have hprev := st118_p48
  have hstep := st118_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p50 : ((25887291085861/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT118 (i+1))
      = (∑ i ∈ Finset.range 49, stT118 (i+1)) + stT118 50 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 49
    simpa using h
  have hprev := st118_p49
  have hstep := st118_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p51 : ((25921831792621/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT118 (i+1))
      = (∑ i ∈ Finset.range 50, stT118 (i+1)) + stT118 51 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 50
    simpa using h
  have hprev := st118_p50
  have hstep := st118_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p52 : ((26940903057871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT118 (i+1))
      = (∑ i ∈ Finset.range 51, stT118 (i+1)) + stT118 52 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 51
    simpa using h
  have hprev := st118_p51
  have hstep := st118_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p53 : ((25582376504539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT118 (i+1))
      = (∑ i ∈ Finset.range 52, stT118 (i+1)) + stT118 53 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 52
    simpa using h
  have hprev := st118_p52
  have hstep := st118_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p54 : ((26218214755327/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT118 (i+1))
      = (∑ i ∈ Finset.range 53, stT118 (i+1)) + stT118 54 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 53
    simpa using h
  have hprev := st118_p53
  have hstep := st118_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p55 : ((6713234294451/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT118 (i+1))
      = (∑ i ∈ Finset.range 54, stT118 (i+1)) + stT118 55 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 54
    simpa using h
  have hprev := st118_p54
  have hstep := st118_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p56 : ((797481385973/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT118 (i+1))
      = (∑ i ∈ Finset.range 55, stT118 (i+1)) + stT118 56 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 55
    simpa using h
  have hprev := st118_p55
  have hstep := st118_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p57 : ((6562126227831/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT118 (i+1))
      = (∑ i ∈ Finset.range 56, stT118 (i+1)) + stT118 57 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 56
    simpa using h
  have hprev := st118_p56
  have hstep := st118_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p58 : ((6721327359447/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT118 (i+1))
      = (∑ i ∈ Finset.range 57, stT118 (i+1)) + stT118 58 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 57
    simpa using h
  have hprev := st118_p57
  have hstep := st118_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p59 : ((6396425087267/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT118 (i+1))
      = (∑ i ∈ Finset.range 58, stT118 (i+1)) + stT118 59 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 58
    simpa using h
  have hprev := st118_p58
  have hstep := st118_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p60 : ((13015610543737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT118 (i+1))
      = (∑ i ∈ Finset.range 59, stT118 (i+1)) + stT118 60 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 59
    simpa using h
  have hprev := st118_p59
  have hstep := st118_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p61 : ((13491747393737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT118 (i+1))
      = (∑ i ∈ Finset.range 60, stT118 (i+1)) + stT118 61 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 60
    simpa using h
  have hprev := st118_p60
  have hstep := st118_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p62 : ((12931670161727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT118 (i+1))
      = (∑ i ∈ Finset.range 61, stT118 (i+1)) + stT118 62 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 61
    simpa using h
  have hprev := st118_p61
  have hstep := st118_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p63 : ((12822861712679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT118 (i+1))
      = (∑ i ∈ Finset.range 62, stT118 (i+1)) + stT118 63 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 62
    simpa using h
  have hprev := st118_p62
  have hstep := st118_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p64 : ((13443776087679/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT118 (i+1))
      = (∑ i ∈ Finset.range 63, stT118 (i+1)) + stT118 64 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 63
    simpa using h
  have hprev := st118_p63
  have hstep := st118_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p65 : ((13217944066797/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT118 (i+1))
      = (∑ i ∈ Finset.range 64, stT118 (i+1)) + stT118 65 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 64
    simpa using h
  have hprev := st118_p64
  have hstep := st118_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p66 : ((25422294869589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT118 (i+1))
      = (∑ i ∈ Finset.range 65, stT118 (i+1)) + stT118 66 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 65
    simpa using h
  have hprev := st118_p65
  have hstep := st118_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p67 : ((26304642592291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT118 (i+1))
      = (∑ i ∈ Finset.range 66, stT118 (i+1)) + stT118 67 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 66
    simpa using h
  have hprev := st118_p66
  have hstep := st118_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p68 : ((26975550632401/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT118 (i+1))
      = (∑ i ∈ Finset.range 67, stT118 (i+1)) + stT118 68 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 67
    simpa using h
  have hprev := st118_p67
  have hstep := st118_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p69 : ((6470867184173/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT118 (i+1))
      = (∑ i ∈ Finset.range 68, stT118 (i+1)) + stT118 69 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 68
    simpa using h
  have hprev := st118_p68
  have hstep := st118_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p70 : ((25521779293773/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT118 (i+1))
      = (∑ i ∈ Finset.range 69, stT118 (i+1)) + stT118 70 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 69
    simpa using h
  have hprev := st118_p69
  have hstep := st118_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p71 : ((26683799294989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT118 (i+1))
      = (∑ i ∈ Finset.range 70, stT118 (i+1)) + stT118 71 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 70
    simpa using h
  have hprev := st118_p70
  have hstep := st118_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p72 : ((6707611238563/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT118 (i+1))
      = (∑ i ∈ Finset.range 71, stT118 (i+1)) + stT118 72 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 71
    simpa using h
  have hprev := st118_p71
  have hstep := st118_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p73 : ((3207834906973/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT118 (i+1))
      = (∑ i ∈ Finset.range 72, stT118 (i+1)) + stT118 73 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 72
    simpa using h
  have hprev := st118_p72
  have hstep := st118_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p74 : ((25623893210679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT118 (i+1))
      = (∑ i ∈ Finset.range 73, stT118 (i+1)) + stT118 74 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 73
    simpa using h
  have hprev := st118_p73
  have hstep := st118_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p75 : ((26778299916879/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT118 (i+1))
      = (∑ i ∈ Finset.range 74, stT118 (i+1)) + stT118 75 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 74
    simpa using h
  have hprev := st118_p74
  have hstep := st118_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p76 : ((1072417045217/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT118 (i+1))
      = (∑ i ∈ Finset.range 75, stT118 (i+1)) + stT118 76 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 75
    simpa using h
  have hprev := st118_p75
  have hstep := st118_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p77 : ((25672571704847/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT118 (i+1))
      = (∑ i ∈ Finset.range 76, stT118 (i+1)) + stT118 77 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 76
    simpa using h
  have hprev := st118_p76
  have hstep := st118_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p78 : ((25554356220257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT118 (i+1))
      = (∑ i ∈ Finset.range 77, stT118 (i+1)) + stT118 78 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 77
    simpa using h
  have hprev := st118_p77
  have hstep := st118_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p79 : ((13331379652567/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT118 (i+1))
      = (∑ i ∈ Finset.range 78, stT118 (i+1)) + stT118 79 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 78
    simpa using h
  have hprev := st118_p78
  have hstep := st118_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p80 : ((26948654877663/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT118 (i+1))
      = (∑ i ∈ Finset.range 79, stT118 (i+1)) + stT118 80 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 79
    simpa using h
  have hprev := st118_p79
  have hstep := st118_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p81 : ((25910119602391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT118 (i+1))
      = (∑ i ∈ Finset.range 80, stT118 (i+1)) + stT118 81 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 80
    simpa using h
  have hprev := st118_p80
  have hstep := st118_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p82 : ((5078751380243/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT118 (i+1))
      = (∑ i ∈ Finset.range 81, stT118 (i+1)) + stT118 82 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 81
    simpa using h
  have hprev := st118_p81
  have hstep := st118_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p83 : ((1051303119957/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT118 (i+1))
      = (∑ i ∈ Finset.range 82, stT118 (i+1)) + stT118 83 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 82
    simpa using h
  have hprev := st118_p82
  have hstep := st118_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p84 : ((5410682111129/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT118 (i+1))
      = (∑ i ∈ Finset.range 83, stT118 (i+1)) + stT118 84 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 83
    simpa using h
  have hprev := st118_p83
  have hstep := st118_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p85 : ((5286064158653/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT118 (i+1))
      = (∑ i ∈ Finset.range 84, stT118 (i+1)) + stT118 85 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 84
    simpa using h
  have hprev := st118_p84
  have hstep := st118_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p86 : ((25446194449017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT118 (i+1))
      = (∑ i ∈ Finset.range 85, stT118 (i+1)) + stT118 86 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 85
    simpa using h
  have hprev := st118_p85
  have hstep := st118_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p87 : ((25674454598601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT118 (i+1))
      = (∑ i ∈ Finset.range 86, stT118 (i+1)) + stT118 87 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 86
    simpa using h
  have hprev := st118_p86
  have hstep := st118_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p88 : ((6685093346091/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT118 (i+1))
      = (∑ i ∈ Finset.range 87, stT118 (i+1)) + stT118 88 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 87
    simpa using h
  have hprev := st118_p87
  have hstep := st118_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p89 : ((1079899577467/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT118 (i+1))
      = (∑ i ∈ Finset.range 88, stT118 (i+1)) + stT118 89 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 88
    simpa using h
  have hprev := st118_p88
  have hstep := st118_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p90 : ((13035537779743/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT118 (i+1))
      = (∑ i ∈ Finset.range 89, stT118 (i+1)) + stT118 90 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 89
    simpa using h
  have hprev := st118_p89
  have hstep := st118_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p91 : ((25345560655841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT118 (i+1))
      = (∑ i ∈ Finset.range 90, stT118 (i+1)) + stT118 91 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 90
    simpa using h
  have hprev := st118_p90
  have hstep := st118_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p92 : ((25868337533801/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT118 (i+1))
      = (∑ i ∈ Finset.range 91, stT118 (i+1)) + stT118 92 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 91
    simpa using h
  have hprev := st118_p91
  have hstep := st118_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p93 : ((13438941477911/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT118 (i+1))
      = (∑ i ∈ Finset.range 92, stT118 (i+1)) + stT118 93 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 92
    simpa using h
  have hprev := st118_p92
  have hstep := st118_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p94 : ((26958768022063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT118 (i+1))
      = (∑ i ∈ Finset.range 93, stT118 (i+1)) + stT118 94 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 93
    simpa using h
  have hprev := st118_p93
  have hstep := st118_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p95 : ((26013991155997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT118 (i+1))
      = (∑ i ∈ Finset.range 94, stT118 (i+1)) + stT118 95 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 94
    simpa using h
  have hprev := st118_p94
  have hstep := st118_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p96 : ((6332222020729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT118 (i+1))
      = (∑ i ∈ Finset.range 95, stT118 (i+1)) + stT118 96 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 95
    simpa using h
  have hprev := st118_p95
  have hstep := st118_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p97 : ((3225495805703/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT118 (i+1))
      = (∑ i ∈ Finset.range 96, stT118 (i+1)) + stT118 97 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 96
    simpa using h
  have hprev := st118_p96
  have hstep := st118_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p98 : ((1675375243413/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT118 (i+1))
      = (∑ i ∈ Finset.range 97, stT118 (i+1)) + stT118 98 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 97
    simpa using h
  have hprev := st118_p97
  have hstep := st118_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p99 : ((6762769034209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT118 (i+1))
      = (∑ i ∈ Finset.range 98, stT118 (i+1)) + stT118 99 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 98
    simpa using h
  have hprev := st118_p98
  have hstep := st118_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st118_p100 : ((6560931784209/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT118 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT118 (i+1))
      = (∑ i ∈ Finset.range 99, stT118 (i+1)) + stT118 100 := by
    have h := Finset.sum_range_succ (fun i => stT118 (i+1)) 99
    simpa using h
  have hprev := st118_p99
  have hstep := st118_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 118`.** -/
theorem station_118_sign : 0 < hardyG (((118:ℕ)):ℝ) := by
  have hcore := phase_station_lower 118 100 (by norm_num) (by norm_num)
    ((136447/250000 : ℚ) : ℝ)
  have hchain := st118_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT118 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((118:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((136447/250000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((118:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((118:ℕ)):ℝ)+1) * ((((118:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((1584263/1180000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((6560931784209/2500000000000 : ℚ) : ℝ) - ((1584263/1180000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((136447/250000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((118:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((136447/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((118:ℕ)):ℝ))).re
      - Real.sin ((136447/250000 : ℚ) : ℝ)
        * (riemannZeta (line (((118:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((118:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((118:ℕ)):ℝ)
      = ((((118:ℕ)):ℝ) * (Real.log (((118:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((118:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_118
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
  have hθwin : |(((136447/250000 : ℚ) : ℝ) + ((18:ℤ)) * (2*Real.pi)) - theta (((118:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((118:ℕ)):ℝ))
    (φ := ((136447/250000 : ℚ) : ℝ) + ((18:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((136447/250000 : ℚ)) : ℝ) 18).1,
    (cos_sin_shift (((136447/250000 : ℚ)) : ℝ) 18).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_118_sign
end AxiomAudit
