import RequestProject.DVPSqrtTable
import RequestProject.DVPLog200Table

/-!
# Station `t = 108` of the extended Hardy ladder (rung-109)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT108 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((108 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-666873/500000 : ℚ) : ℝ))

theorem st108_c1 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((58709/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 666873/2000000) (δ := 1/100000000) (ψ := -666873/500000) 108 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t1 : ((117393/500000 : ℚ) : ℝ) ≤ stT108 1 := by
  have hc : ((117393/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117393/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((117393/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c2 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((699987/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31071/156250) (δ := 17/2000000) (ψ := -666873/500000) 108 12
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t2 : ((4949301422779/10000000000000 : ℚ) : ℝ) ≤ stT108 2 := by
  have hc : ((699937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4949301422779/10000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((699937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c3 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((411719/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 75419/500000) (δ := 37/4000000) (ψ := -666873/500000) 108 19
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t3 : ((594229033097/1250000000000 : ℚ) : ℝ) ≤ stT108 3 := by
  have hc : ((205847/250000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((594229033097/1250000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((205847/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c4 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((483567/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 160681/2500000) (δ := 659/100000000) (ψ := -666873/500000) 108 24
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t4 : ((241771/500000 : ℚ) : ℝ) ≤ stT108 4 := by
  have hc : ((241771/250000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241771/500000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((241771/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c5 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((713617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1940371/10000000) (δ := 981/100000000) (ψ := -666873/500000) 108 28
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t5 : ((638233591109/2000000000000 : ℚ) : ℝ) ≤ stT108 5 := by
  have hc : ((713567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((638233591109/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((713567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c6 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((997887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 254/15625) (δ := 367/50000000) (ψ := -666873/500000) 108 31
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t6 : ((2036825795717/5000000000000 : ℚ) : ℝ) ≤ stT108 6 := by
  have hc : ((997837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2036825795717/5000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((997837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c7 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-267903/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2670323/5000000) (δ := 557/100000000) (ψ := -666873/500000) 108 34
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t7 : ((-25316818139/125000000000 : ℚ) : ℝ) ≤ stT108 7 := by
  have hc : ((-33491/62500 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).2
  have h0 : (0:ℝ) ≤ ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25316818139/125000000000 : ℚ) : ℝ)
      = ((755929/2000000 : ℚ) : ℝ) * ((-33491/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c8 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((120089/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -703097/10000000) (δ := 41/6250000) (ψ := -666873/500000) 108 36
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t8 : ((1698226101423/5000000000000 : ℚ) : ℝ) ≤ stT108 8 := by
  have hc : ((480331/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1698226101423/5000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((480331/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c9 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((991941/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79401/2500000) (δ := 809/100000000) (ψ := -666873/500000) 108 38
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t9 : ((3306303002703/10000000000000 : ℚ) : ℝ) ≤ stT108 9 := by
  have hc : ((991891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3306303002703/10000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((991891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c10 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((126761/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3286191/10000000) (δ := 99/10000000) (ψ := -666873/500000) 108 40
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t10 : ((25048396117/312500000000 : ℚ) : ℝ) ≤ stT108 10 := by
  have hc : ((7921/31250 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((25048396117/312500000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((7921/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c11 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-180457/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3369797/5000000) (δ := 761/100000000) (ψ := -666873/500000) 108 41
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t11 : ((-272064289119/1000000000000 : ℚ) : ℝ) ≤ stT108 11 := by
  have hc : ((-180467/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-272064289119/1000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-180467/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c12 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((890067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1183261/10000000) (δ := 581/100000000) (ψ := -666873/500000) 108 43
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t12 : ((2569257464767/10000000000000 : ℚ) : ℝ) ≤ stT108 12 := by
  have hc : ((890017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2569257464767/10000000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((890017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c13 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-78007/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4720307/10000000) (δ := 593/100000000) (ψ := -666873/500000) 108 44
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t13 : ((-432774322539/5000000000000 : ℚ) : ℝ) ≤ stT108 13 := by
  have hc : ((-156039/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-432774322539/5000000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-156039/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c14 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-22323/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6686467/10000000) (δ := 197/25000000) (ψ := -666873/500000) 108 46
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t14 : ((-238656323061/1000000000000 : ℚ) : ℝ) ≤ stT108 14 := by
  have hc : ((-89297/100000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-238656323061/1000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-89297/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c15 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((6421/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -753271/2000000) (δ := 549/50000000) (ψ := -666873/500000) 108 47
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t15 : ((258844297/15625000000 : ℚ) : ℝ) ≤ stT108 15 := by
  have hc : ((401/6250 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).1
  have hw2 : ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((258844297/15625000000 : ℚ) : ℝ)
      = ((645497/2500000 : ℚ) : ℝ) * ((401/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c16 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((341269/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2048917/10000000) (δ := 847/100000000) (ψ := -666873/500000) 108 48
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t16 : ((85311/500000 : ℚ) : ℝ) ≤ stT108 16 := by
  have hc : ((85311/125000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85311/500000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((85311/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c17 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((424873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1388233/10000000) (δ := 159/25000000) (ψ := -666873/500000) 108 49
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t17 : ((16100119467/78125000000 : ℚ) : ℝ) ≤ stT108 17 := by
  have hc : ((26553/31250 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16100119467/78125000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((26553/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c18 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((786689/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -25991/156250) (δ := 617/100000000) (ψ := -666873/500000) 108 50
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t18 : ((927062714529/5000000000000 : ℚ) : ℝ) ≤ stT108 18 := by
  have hc : ((786639/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((927062714529/5000000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((786639/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c19 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((445293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1386619/5000000) (δ := 207/25000000) (ψ := -666873/500000) 108 51
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t19 : ((1021457345151/10000000000000 : ℚ) : ℝ) ≤ stT108 19 := by
  have hc : ((445243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1021457345151/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((445243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c20 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-55657/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1158003/2500000) (δ := 759/100000000) (ψ := -666873/500000) 108 52
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t20 : ((-31118799339/500000000000 : ℚ) : ℝ) ≤ stT108 20 := by
  have hc : ((-55667/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-31118799339/500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-55667/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c21 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-962441/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7166631/10000000) (δ := 713/100000000) (ψ := -666873/500000) 108 53
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t21 : ((-2100327647889/10000000000000 : ℚ) : ℝ) ≤ stT108 21 := by
  have hc : ((-962491/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2100327647889/10000000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-962491/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c22 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-553627/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2696887/5000000) (δ := 57/10000000) (ψ := -666873/500000) 108 53
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t22 : ((-147555474177/1250000000000 : ℚ) : ℝ) ≤ stT108 22 := by
  have hc : ((-553677/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147555474177/1250000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-553677/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c23 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((156127/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 843893/5000000) (δ := 943/100000000) (ψ := -666873/500000) 108 54
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t23 : ((40690803231/250000000000 : ℚ) : ℝ) ≤ stT108 23 := by
  have hc : ((156117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((40690803231/250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((156117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c24 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((265239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2529081/10000000) (δ := 193/25000000) (ψ := -666873/500000) 108 55
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t24 : ((270682845287/2500000000000 : ℚ) : ℝ) ≤ stT108 24 := by
  have hc : ((132607/250000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((270682845287/2500000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((132607/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c25 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-241881/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3607553/5000000) (δ := 841/100000000) (ψ := -666873/500000) 108 56
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t25 : ((-967574483787/5000000000000 : ℚ) : ℝ) ≤ stT108 25 := by
  have hc : ((-483787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).2
  have h0 : (0:ℝ) ≤ ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-967574483787/5000000000000 : ℚ) : ℝ)
      = ((2000001/10000000 : ℚ) : ℝ) * ((-483787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c26 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((219207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3374487/10000000) (δ := 681/100000000) (ψ := -666873/500000) 108 56
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t26 : ((429802161277/10000000000000 : ℚ) : ℝ) ≤ stT108 26 := by
  have hc : ((219157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((429802161277/10000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((219157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c27 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((654379/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -535897/2500000) (δ := 173/25000000) (ψ := -666873/500000) 108 57
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t27 : ((2518512321/20000000000 : ℚ) : ℝ) ≤ stT108 27 := by
  have hc : ((654329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2518512321/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((654329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c28 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-498729/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1918919/2500000) (δ := 991/100000000) (ψ := -666873/500000) 108 57
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t28 : ((-471278390271/2500000000000 : ℚ) : ℝ) ≤ stT108 28 := by
  have hc : ((-249377/250000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).2
  have h0 : (0:ℝ) ≤ ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-471278390271/2500000000000 : ℚ) : ℝ)
      = ((1889823/10000000 : ℚ) : ℝ) * ((-249377/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c29 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((209533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1442369/10000000) (δ := 39/5000000) (ψ := -666873/500000) 108 58
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t29 : ((778139442073/5000000000000 : ℚ) : ℝ) ≤ stT108 29 := by
  have hc : ((419041/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((778139442073/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((419041/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c30 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-228257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -204487/400000) (δ := 437/50000000) (ψ := -666873/500000) 108 59
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t30 : ((-104196008811/1250000000000 : ℚ) : ℝ) ≤ stT108 30 := by
  have hc : ((-114141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104196008811/1250000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-114141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c31 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((74297/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3741077/10000000) (δ := 1049/100000000) (ψ := -666873/500000) 108 59
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t31 : ((133351547091/10000000000000 : ℚ) : ℝ) ≤ stT108 31 := by
  have hc : ((74247/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133351547091/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((74247/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c32 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((6603/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1697369/5000000) (δ := 539/50000000) (ψ := -666873/500000) 108 60
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t32 : ((93358374109/2500000000000 : ℚ) : ℝ) ≤ stT108 32 := by
  have hc : ((105623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((93358374109/2500000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((105623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c33 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-384483/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 491361/1000000) (δ := 129/20000000) (ψ := -666873/500000) 108 60
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t33 : ((-669386202141/10000000000000 : ℚ) : ℝ) ≤ stT108 33 := by
  have hc : ((-384533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-669386202141/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-384533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c34 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((57409/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2734053/10000000) (δ := 207/25000000) (ψ := -666873/500000) 108 61
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t34 : ((78755884167/1000000000000 : ℚ) : ℝ) ≤ stT108 34 := by
  have hc : ((229611/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78755884167/1000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((229611/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c35 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-56191/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2546291/5000000) (δ := 131/20000000) (ψ := -666873/500000) 108 61
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t35 : ((-379962869801/5000000000000 : ℚ) : ℝ) ≤ stT108 35 := by
  have hc : ((-224789/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379962869801/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-224789/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c36 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((358909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -601849/2000000) (δ := 697/100000000) (ψ := -666873/500000) 108 62
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t36 : ((299049047047/5000000000000 : ℚ) : ℝ) ≤ stT108 36 := by
  have hc : ((358859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((299049047047/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((358859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c37 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-45887/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2194239/5000000) (δ := 977/100000000) (ψ := -666873/500000) 108 62
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t37 : ((-15091663801/500000000000 : ℚ) : ℝ) ≤ stT108 37 := by
  have hc : ((-91799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15091663801/500000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-91799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c38 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-76751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2059529/5000000) (δ := 637/100000000) (ψ := -666873/500000) 108 63
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t38 : ((-24917546843/2000000000000 : ℚ) : ℝ) ≤ stT108 38 := by
  have hc : ((-76801/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-24917546843/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-76801/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c39 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((20071/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2894323/10000000) (δ := 303/50000000) (ψ := -666873/500000) 108 63
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t39 : ((64270615497/1000000000000 : ℚ) : ℝ) ≤ stT108 39 := by
  have hc : ((40137/100000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((64270615497/1000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((40137/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c40 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-5851/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -747229/1250000) (δ := 567/100000000) (ψ := -666873/500000) 108 64
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t40 : ((-46259383723/400000000000 : ℚ) : ℝ) ≤ stT108 40 := by
  have hc : ((-29257/40000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-46259383723/400000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-29257/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c41 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((962243/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689173/10000000) (δ := 687/100000000) (ψ := -666873/500000) 108 64
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t41 : ((1502692409241/10000000000000 : ℚ) : ℝ) ≤ stT108 41 := by
  have hc : ((962193/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1502692409241/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((962193/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c42 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-965513/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 899439/1250000) (δ := 229/25000000) (ψ := -666873/500000) 108 64
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t42 : ((-744948269071/5000000000000 : ℚ) : ℝ) ≤ stT108 42 := by
  have hc : ((-965563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-744948269071/5000000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-965563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c43 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((649639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2159217/10000000) (δ := 189/20000000) (ψ := -666873/500000) 108 65
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t43 : ((198122696233/2000000000000 : ℚ) : ℝ) ≤ stT108 43 := by
  have hc : ((649589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((198122696233/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((649589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c44 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-24183/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4047953/10000000) (δ := 149/20000000) (ψ := -666873/500000) 108 65
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t44 : ((-2280933741/312500000000 : ℚ) : ℝ) ≤ stT108 44 := by
  have hc : ((-1513/31250 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2280933741/312500000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-1513/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c45 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-123591/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5592339/10000000) (δ := 949/100000000) (ψ := -666873/500000) 108 66
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t45 : ((-23031686739/250000000000 : ℚ) : ℝ) ≤ stT108 45 := by
  have hc : ((-123601/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23031686739/250000000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-123601/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c46 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((990659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170983/5000000) (δ := 1029/100000000) (ψ := -666873/500000) 108 66
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t46 : ((1460572731171/10000000000000 : ℚ) : ℝ) ≤ stT108 46 := by
  have hc : ((990609/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1460572731171/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((990609/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c47 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-194057/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6148641/10000000) (δ := 547/50000000) (ψ := -666873/500000) 108 66
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t47 : ((-11323179047/100000000000 : ℚ) : ℝ) ≤ stT108 47 := by
  have hc : ((-388139/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11323179047/100000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-388139/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c48 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((10417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1937451/5000000) (δ := 1003/100000000) (ψ := -666873/500000) 108 67
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t48 : ((14999553/5000000000 : ℚ) : ℝ) ≤ stT108 48 := by
  have hc : ((1299/62500 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14999553/5000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((1299/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c49 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((48719/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 846153/5000000) (δ := 13/1250000) (ψ := -666873/500000) 108 67
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t49 : ((556752690117/5000000000000 : ℚ) : ℝ) ≤ stT108 49 := by
  have hc : ((389727/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((556752690117/5000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((389727/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c50 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-240071/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7147037/10000000) (δ := 1043/100000000) (ψ := -666873/500000) 108 67
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t50 : ((-339529446869/2500000000000 : ℚ) : ℝ) ≤ stT108 50 := by
  have hc : ((-480167/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-339529446869/2500000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-480167/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c51 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((281263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3214217/10000000) (δ := 753/100000000) (ψ := -666873/500000) 108 68
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t51 : ((9844423491/250000000000 : ℚ) : ℝ) ≤ stT108 51 := by
  have hc : ((281213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9844423491/250000000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((281213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c52 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((172109/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1014333/5000000) (δ := 913/100000000) (ψ := -666873/500000) 108 68
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t52 : ((1909238571/20000000000 : ℚ) : ℝ) ≤ stT108 52 := by
  have hc : ((344193/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1909238571/20000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((344193/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c53 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-240747/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7171679/10000000) (δ := 953/100000000) (ψ := -666873/500000) 108 68
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t53 : ((-330708693757/2500000000000 : ℚ) : ℝ) ≤ stT108 53 := by
  have hc : ((-481519/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-330708693757/2500000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-481519/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c54 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((174141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -27261/78125) (δ := 291/50000000) (ψ := -666873/500000) 108 69
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t54 : ((236907733257/10000000000000 : ℚ) : ℝ) ≤ stT108 54 := by
  have hc : ((174091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((236907733257/10000000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((174091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c55 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((833191/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1464859/10000000) (δ := 901/100000000) (ψ := -666873/500000) 108 69
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t55 : ((1123406491259/10000000000000 : ℚ) : ℝ) ≤ stT108 55 := by
  have hc : ((833141/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1123406491259/10000000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((833141/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c56 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-102481/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 49452/78125) (δ := 981/100000000) (ψ := -666873/500000) 108 69
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t56 : ((-547817718343/5000000000000 : ℚ) : ℝ) ≤ stT108 56 := by
  have hc : ((-409949/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547817718343/5000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-409949/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c57 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-4151/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2299611/5000000) (δ := 89/12500000) (ψ := -666873/500000) 108 70
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t57 : ((-175973480781/5000000000000 : ℚ) : ℝ) ≤ stT108 57 := by
  have hc : ((-132857/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-175973480781/5000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-132857/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c58 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((499627/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 96549/10000000) (δ := 971/100000000) (ψ := -666873/500000) 108 70
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t58 : ((41000587533/312500000000 : ℚ) : ℝ) ≤ stT108 58 := by
  have hc : ((249801/250000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((41000587533/312500000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((249801/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c59 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-308887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2356023/5000000) (δ := 611/100000000) (ψ := -666873/500000) 108 70
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t59 : ((-40220199093/1000000000000 : ℚ) : ℝ) ≤ stT108 59 := by
  have hc : ((-308937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).2
  have h0 : (0:ℝ) ≤ ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40220199093/1000000000000 : ℚ) : ℝ)
      = ((130189/1000000 : ℚ) : ℝ) * ((-308937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c60 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-848107/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1614499/2500000) (δ := 321/50000000) (ψ := -666873/500000) 108 71
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t60 : ((-218993289243/2000000000000 : ℚ) : ℝ) ≤ stT108 60 := by
  have hc : ((-848157/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218993289243/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-848157/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c61 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((174529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -498771/2500000) (δ := 341/50000000) (ψ := -666873/500000) 108 71
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t61 : ((27930667759/312500000000 : ℚ) : ℝ) ≤ stT108 61 := by
  have hc : ((349033/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27930667759/312500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((349033/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c62 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((575073/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 299407/1250000) (δ := 441/50000000) (ψ := -666873/500000) 108 71
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t62 : ((730279785023/10000000000000 : ℚ) : ℝ) ≤ stT108 62 := by
  have hc : ((575023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).1
  have hw2 : ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1270001/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((730279785023/10000000000000 : ℚ) : ℝ)
      = ((1270001/10000000 : ℚ) : ℝ) * ((575023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c63 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-449031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6715349/10000000) (δ := 801/100000000) (ψ := -666873/500000) 108 71
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t63 : ((-8839962053/78125000000 : ℚ) : ℝ) ≤ stT108 63 := by
  have hc : ((-14033/15625 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8839962053/78125000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-14033/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c64 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-319713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2370279/5000000) (δ := 893/100000000) (ψ := -666873/500000) 108 72
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t64 : ((-399704069763/10000000000000 : ℚ) : ℝ) ≤ stT108 64 := by
  have hc : ((-319763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-399704069763/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-319763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c65 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((975509/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -138607/2500000) (δ := 733/100000000) (ψ := -666873/500000) 108 72
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t65 : ((1209907644273/10000000000000 : ℚ) : ℝ) ≤ stT108 65 := by
  have hc : ((975459/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).1
  have hw2 : ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1240347/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1209907644273/10000000000000 : ℚ) : ℝ)
      = ((1240347/10000000 : ℚ) : ℝ) * ((975459/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c66 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((71593/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 356779/1000000) (δ := 63/10000000) (ψ := -666873/500000) 108 72
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t66 : ((2752939161/156250000000 : ℚ) : ℝ) ≤ stT108 66 := by
  have hc : ((4473/31250 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2752939161/156250000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((4473/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c67 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-497959/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 476751/625000) (δ := 91/10000000) (ψ := -666873/500000) 108 72
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t67 : ((-1901201759/15625000000 : ℚ) : ℝ) ≤ stT108 67 := by
  have hc : ((-15562/15625 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1901201759/15625000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-15562/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c68 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-12223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2039937/5000000) (δ := 1059/100000000) (ψ := -666873/500000) 108 73
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t68 : ((-14834702207/2000000000000 : ℚ) : ℝ) ≤ stT108 68 := by
  have hc : ((-12233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14834702207/2000000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-12233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c69 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((124809/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -69099/5000000) (δ := 1059/100000000) (ψ := -666873/500000) 108 73
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t69 : ((300489578019/2500000000000 : ℚ) : ℝ) ≤ stT108 69 := by
  have hc : ((499211/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((300489578019/2500000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((499211/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c70 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((72029/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3746761/10000000) (δ := 659/100000000) (ψ := -666873/500000) 108 73
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t70 : ((21507829053/2500000000000 : ℚ) : ℝ) ≤ stT108 70 := by
  have hc : ((71979/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21507829053/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((71979/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c71 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-248463/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7576613/10000000) (δ := 103/12500000) (ψ := -666873/500000) 108 73
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t71 : ((-294886250841/2500000000000 : ℚ) : ℝ) ≤ stT108 71 := by
  have hc : ((-496951/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-294886250841/2500000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-496951/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c72 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-85197/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -871013/2000000) (δ := 111/12500000) (ψ := -666873/500000) 108 74
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t72 : ((-3138598427/156250000000 : ℚ) : ℝ) ≤ stT108 72 := by
  have hc : ((-42611/250000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3138598427/156250000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-42611/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c73 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((968329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157717/2500000) (δ := 81/12500000) (ψ := -666873/500000) 108 74
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t73 : ((1133284392669/10000000000000 : ℚ) : ℝ) ≤ stT108 73 := by
  have hc : ((968279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1133284392669/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((968279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c74 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((173201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1521329/5000000) (δ := 199/20000000) (ψ := -666873/500000) 108 74
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t74 : ((6291029493/156250000000 : ℚ) : ℝ) ≤ stT108 74 := by
  have hc : ((21647/62500 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6291029493/156250000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((21647/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c75 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-222341/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6666873/10000000) (δ := 121/12500000) (ψ := -666873/500000) 108 74
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t75 : ((-513503617607/5000000000000 : ℚ) : ℝ) ≤ stT108 75 := by
  have hc : ((-444707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-513503617607/5000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-444707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c76 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-115417/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5464879/10000000) (δ := 339/50000000) (ψ := -666873/500000) 108 75
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t76 : ((-132403887733/2000000000000 : ℚ) : ℝ) ≤ stT108 76 := by
  have hc : ((-115427/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-132403887733/2000000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-115427/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c77 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((178751/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1935417/10000000) (δ := 439/50000000) (ψ := -666873/500000) 108 75
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t77 : ((81476515317/1000000000000 : ℚ) : ℝ) ≤ stT108 77 := by
  have hc : ((357477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).1
  have hw2 : ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((227921/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81476515317/1000000000000 : ℚ) : ℝ)
      = ((227921/2000000 : ℚ) : ℝ) * ((357477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c78 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((407113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1548503/10000000) (δ := 399/50000000) (ψ := -666873/500000) 108 75
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t78 : ((28808523711/312500000000 : ℚ) : ℝ) ≤ stT108 78 := by
  have hc : ((25443/31250 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28808523711/312500000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((25443/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c79 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-25737/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124701/250000) (δ := 113/20000000) (ψ := -666873/500000) 108 75
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t79 : ((-7239976439/156250000000 : ℚ) : ℝ) ≤ stT108 79 := by
  have hc : ((-205921/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7239976439/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-205921/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c80 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-61099/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7323653/10000000) (δ := 747/100000000) (ψ := -666873/500000) 108 76
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t80 : ((-273257012889/2500000000000 : ℚ) : ℝ) ≤ stT108 80 := by
  have hc : ((-488817/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-273257012889/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-488817/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c81 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-2129/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -992393/2500000) (δ := 9/1562500) (ψ := -666873/500000) 108 76
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t81 : ((-1186250949/625000000000 : ℚ) : ℝ) ≤ stT108 81 := by
  have hc : ((-8541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).2
  have h0 : (0:ℝ) ≤ ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1186250949/625000000000 : ℚ) : ℝ)
      = ((138889/1250000 : ℚ) : ℝ) * ((-8541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c82 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((965703/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -656647/10000000) (δ := 587/100000000) (ψ := -666873/500000) 108 76
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t82 : ((213277018539/2000000000000 : ℚ) : ℝ) ≤ stT108 82 := by
  have hc : ((965653/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((213277018539/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((965653/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c83 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((500649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65403/250000) (δ := 1027/100000000) (ψ := -666873/500000) 108 76
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t83 : ((274739243779/5000000000000 : ℚ) : ℝ) ≤ stT108 83 := by
  have hc : ((500599/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274739243779/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((500599/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c84 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-27819/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1462423/2500000) (δ := 1107/100000000) (ψ := -666873/500000) 108 76
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t84 : ((-3035521489/40000000000 : ℚ) : ℝ) ≤ stT108 84 := by
  have hc : ((-27821/40000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3035521489/40000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-27821/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c85 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-888649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -832871/1250000) (δ := 587/100000000) (ψ := -666873/500000) 108 77
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t85 : ((-963930036447/10000000000000 : ℚ) : ℝ) ≤ stT108 85 := by
  have hc : ((-888699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-963930036447/10000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-888699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c86 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((167981/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3505037/10000000) (δ := 1027/100000000) (ψ := -666873/500000) 108 77
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t86 : ((181084531437/10000000000000 : ℚ) : ℝ) ≤ stT108 86 := by
  have hc : ((167931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).1
  have hw2 : ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1078327/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181084531437/10000000000000 : ℚ) : ℝ)
      = ((1078327/10000000 : ℚ) : ℝ) * ((167931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c87 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((3953/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -76723/2000000) (δ := 7/781250) (ψ := -666873/500000) 108 77
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t87 : ((331081587/3125000000 : ℚ) : ℝ) ≤ stT108 87 := by
  have hc : ((4941/5000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331081587/3125000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((4941/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c88 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((29411/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2702133/10000000) (δ := 117/12500000) (ψ := -666873/500000) 108 77
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t88 : ((250791063789/5000000000000 : ℚ) : ℝ) ≤ stT108 88 := by
  have hc : ((235263/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((250791063789/5000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((235263/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c89 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-333587/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5753013/10000000) (δ := 747/100000000) (ψ := -666873/500000) 108 77
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t89 : ((-44203506597/625000000000 : ℚ) : ℝ) ≤ stT108 89 := by
  have hc : ((-83403/125000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44203506597/625000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-83403/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c90 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-933649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6938159/10000000) (δ := 379/50000000) (ψ := -666873/500000) 108 78
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t90 : ((-984205580007/10000000000000 : ℚ) : ℝ) ≤ stT108 90 := by
  have hc : ((-933699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-984205580007/10000000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-933699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c91 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-2217/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247169/625000) (δ := 559/50000000) (ψ := -666873/500000) 108 78
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t91 : ((-466906139/400000000000 : ℚ) : ℝ) ≤ stT108 91 := by
  have hc : ((-2227/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-466906139/400000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-2227/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c92 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((920459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -200771/2000000) (δ := 399/50000000) (ψ := -666873/500000) 108 78
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t92 : ((239898162987/2500000000000 : ℚ) : ℝ) ≤ stT108 92 := by
  have hc : ((920409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((239898162987/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((920409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c93 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((90083/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1915093/10000000) (δ := 499/50000000) (ψ := -666873/500000) 108 78
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t93 : ((373620703957/5000000000000 : ℚ) : ℝ) ≤ stT108 93 := by
  have hc : ((360307/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373620703957/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((360307/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c94 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-34321/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4802821/10000000) (δ := 439/50000000) (ψ := -666873/500000) 108 78
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t94 : ((-8851147893/250000000000 : ℚ) : ℝ) ≤ stT108 94 := by
  have hc : ((-17163/50000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8851147893/250000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-17163/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c95 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-996991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 765999/1000000) (δ := 479/50000000) (ψ := -666873/500000) 108 78
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t95 : ((-1022943128139/10000000000000 : ℚ) : ℝ) ≤ stT108 95 := by
  have hc : ((-997041/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1022943128139/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-997041/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c96 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-247351/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2610361/5000000) (δ := 121/12500000) (ψ := -666873/500000) 108 79
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t96 : ((-15779821281/312500000000 : ℚ) : ℝ) ≤ stT108 96 := by
  have hc : ((-15461/31250 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15779821281/312500000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-15461/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c97 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((113207/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2422769/10000000) (δ := 53/6250000) (ψ := -666873/500000) 108 79
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t97 : ((57467060581/1000000000000 : ℚ) : ℝ) ≤ stT108 97 := by
  have hc : ((113197/200000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57467060581/1000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((113197/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c98 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((990411/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173243/5000000) (δ := 53/6250000) (ψ := -666873/500000) 108 79
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t98 : ((125051893109/1250000000000 : ℚ) : ℝ) ≤ stT108 98 := by
  have hc : ((990361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((125051893109/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((990361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c99 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((164737/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1543813/5000000) (δ := 111/20000000) (ψ := -666873/500000) 108 79
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t99 : ((20692706793/625000000000 : ℚ) : ℝ) ≤ stT108 99 := by
  have hc : ((20589/62500 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).1
  have hw2 : ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1005037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20692706793/625000000000 : ℚ) : ℝ)
      = ((1005037/10000000 : ℚ) : ℝ) * ((20589/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_c100 :
    |Real.cos (((108 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-666873/500000 : ℚ) : ℝ))
      - ((-170353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5801217/10000000) (δ := 29/3125000) (ψ := -666873/500000) 108 79
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st108_t100 : ((-340731/5000000 : ℚ) : ℝ) ≤ stT108 100 := by
  have hc : ((-340731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((108 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-666873/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st108_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).2
  have h0 : (0:ℝ) ≤ ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340731/5000000 : ℚ) : ℝ)
      = ((1/10 : ℚ) : ℝ) * ((-340731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st108_p1 : ((117393/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT108 (i+1) := by
  rw [Finset.sum_range_one]
  exact st108_t1

theorem st108_p2 : ((7297161422779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT108 (i+1))
      = (∑ i ∈ Finset.range 1, stT108 (i+1)) + stT108 2 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 1
    simpa using h
  have hprev := st108_p1
  have hstep := st108_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p3 : ((2410198737511/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT108 (i+1))
      = (∑ i ∈ Finset.range 2, stT108 (i+1)) + stT108 3 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 2
    simpa using h
  have hprev := st108_p2
  have hstep := st108_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p4 : ((3377282737511/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT108 (i+1))
      = (∑ i ∈ Finset.range 3, stT108 (i+1)) + stT108 4 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 3
    simpa using h
  have hprev := st108_p3
  have hstep := st108_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p5 : ((200775816431/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT108 (i+1))
      = (∑ i ∈ Finset.range 4, stT108 (i+1)) + stT108 5 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 4
    simpa using h
  have hprev := st108_p4
  have hstep := st108_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p6 : ((12075616617267/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT108 (i+1))
      = (∑ i ∈ Finset.range 5, stT108 (i+1)) + stT108 6 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 5
    simpa using h
  have hprev := st108_p5
  have hstep := st108_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p7 : ((11062943891707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT108 (i+1))
      = (∑ i ∈ Finset.range 6, stT108 (i+1)) + stT108 7 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 6
    simpa using h
  have hprev := st108_p6
  have hstep := st108_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p8 : ((1276116999313/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT108 (i+1))
      = (∑ i ∈ Finset.range 7, stT108 (i+1)) + stT108 8 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 7
    simpa using h
  have hprev := st108_p7
  have hstep := st108_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p9 : ((28828642988963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT108 (i+1))
      = (∑ i ∈ Finset.range 8, stT108 (i+1)) + stT108 9 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 8
    simpa using h
  have hprev := st108_p8
  have hstep := st108_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p10 : ((29630191664707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT108 (i+1))
      = (∑ i ∈ Finset.range 9, stT108 (i+1)) + stT108 10 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 9
    simpa using h
  have hprev := st108_p9
  have hstep := st108_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p11 : ((26909548773517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT108 (i+1))
      = (∑ i ∈ Finset.range 10, stT108 (i+1)) + stT108 11 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 10
    simpa using h
  have hprev := st108_p10
  have hstep := st108_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p12 : ((7369701559571/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT108 (i+1))
      = (∑ i ∈ Finset.range 11, stT108 (i+1)) + stT108 12 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 11
    simpa using h
  have hprev := st108_p11
  have hstep := st108_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p13 : ((14306628796603/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT108 (i+1))
      = (∑ i ∈ Finset.range 12, stT108 (i+1)) + stT108 13 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 12
    simpa using h
  have hprev := st108_p12
  have hstep := st108_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p14 : ((6556673590649/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT108 (i+1))
      = (∑ i ∈ Finset.range 13, stT108 (i+1)) + stT108 14 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 13
    simpa using h
  have hprev := st108_p13
  have hstep := st108_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p15 : ((6598088678169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT108 (i+1))
      = (∑ i ∈ Finset.range 14, stT108 (i+1)) + stT108 15 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 14
    simpa using h
  have hprev := st108_p14
  have hstep := st108_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p16 : ((7024643678169/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT108 (i+1))
      = (∑ i ∈ Finset.range 15, stT108 (i+1)) + stT108 16 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 15
    simpa using h
  have hprev := st108_p15
  have hstep := st108_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p17 : ((7539847501113/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT108 (i+1))
      = (∑ i ∈ Finset.range 16, stT108 (i+1)) + stT108 17 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 16
    simpa using h
  have hprev := st108_p16
  have hstep := st108_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p18 : ((3201351543351/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT108 (i+1))
      = (∑ i ∈ Finset.range 17, stT108 (i+1)) + stT108 18 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 17
    simpa using h
  have hprev := st108_p17
  have hstep := st108_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p19 : ((33034972778661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT108 (i+1))
      = (∑ i ∈ Finset.range 18, stT108 (i+1)) + stT108 19 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 18
    simpa using h
  have hprev := st108_p18
  have hstep := st108_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p20 : ((32412596791881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT108 (i+1))
      = (∑ i ∈ Finset.range 19, stT108 (i+1)) + stT108 20 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 19
    simpa using h
  have hprev := st108_p19
  have hstep := st108_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p21 : ((3789033642999/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT108 (i+1))
      = (∑ i ∈ Finset.range 20, stT108 (i+1)) + stT108 21 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 20
    simpa using h
  have hprev := st108_p20
  have hstep := st108_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p22 : ((1820739084411/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT108 (i+1))
      = (∑ i ∈ Finset.range 21, stT108 (i+1)) + stT108 22 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 21
    simpa using h
  have hprev := st108_p21
  have hstep := st108_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p23 : ((3844932184977/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT108 (i+1))
      = (∑ i ∈ Finset.range 22, stT108 (i+1)) + stT108 23 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 22
    simpa using h
  have hprev := st108_p22
  have hstep := st108_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p24 : ((7960547215241/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT108 (i+1))
      = (∑ i ∈ Finset.range 23, stT108 (i+1)) + stT108 24 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 23
    simpa using h
  have hprev := st108_p23
  have hstep := st108_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p25 : ((2990703989339/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT108 (i+1))
      = (∑ i ∈ Finset.range 24, stT108 (i+1)) + stT108 25 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 24
    simpa using h
  have hprev := st108_p24
  have hstep := st108_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p26 : ((30336842054667/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT108 (i+1))
      = (∑ i ∈ Finset.range 25, stT108 (i+1)) + stT108 26 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 25
    simpa using h
  have hprev := st108_p25
  have hstep := st108_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p27 : ((31596098215167/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT108 (i+1))
      = (∑ i ∈ Finset.range 26, stT108 (i+1)) + stT108 27 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 26
    simpa using h
  have hprev := st108_p26
  have hstep := st108_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p28 : ((29710984654083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT108 (i+1))
      = (∑ i ∈ Finset.range 27, stT108 (i+1)) + stT108 28 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 27
    simpa using h
  have hprev := st108_p27
  have hstep := st108_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p29 : ((31267263538229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT108 (i+1))
      = (∑ i ∈ Finset.range 28, stT108 (i+1)) + stT108 29 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 28
    simpa using h
  have hprev := st108_p28
  have hstep := st108_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p30 : ((30433695467741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT108 (i+1))
      = (∑ i ∈ Finset.range 29, stT108 (i+1)) + stT108 30 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 29
    simpa using h
  have hprev := st108_p29
  have hstep := st108_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p31 : ((1910440438427/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT108 (i+1))
      = (∑ i ∈ Finset.range 30, stT108 (i+1)) + stT108 31 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 30
    simpa using h
  have hprev := st108_p30
  have hstep := st108_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p32 : ((7735120127817/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT108 (i+1))
      = (∑ i ∈ Finset.range 31, stT108 (i+1)) + stT108 32 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 31
    simpa using h
  have hprev := st108_p31
  have hstep := st108_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p33 : ((30271094309127/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT108 (i+1))
      = (∑ i ∈ Finset.range 32, stT108 (i+1)) + stT108 33 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 32
    simpa using h
  have hprev := st108_p32
  have hstep := st108_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p34 : ((31058653150797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT108 (i+1))
      = (∑ i ∈ Finset.range 33, stT108 (i+1)) + stT108 34 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 33
    simpa using h
  have hprev := st108_p33
  have hstep := st108_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p35 : ((6059745482239/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT108 (i+1))
      = (∑ i ∈ Finset.range 34, stT108 (i+1)) + stT108 35 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 34
    simpa using h
  have hprev := st108_p34
  have hstep := st108_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p36 : ((30896825505289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT108 (i+1))
      = (∑ i ∈ Finset.range 35, stT108 (i+1)) + stT108 36 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 35
    simpa using h
  have hprev := st108_p35
  have hstep := st108_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p37 : ((30594992229269/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT108 (i+1))
      = (∑ i ∈ Finset.range 36, stT108 (i+1)) + stT108 37 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 36
    simpa using h
  have hprev := st108_p36
  have hstep := st108_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p38 : ((15235202247527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT108 (i+1))
      = (∑ i ∈ Finset.range 37, stT108 (i+1)) + stT108 38 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 37
    simpa using h
  have hprev := st108_p37
  have hstep := st108_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p39 : ((3889138831253/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT108 (i+1))
      = (∑ i ∈ Finset.range 38, stT108 (i+1)) + stT108 39 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 38
    simpa using h
  have hprev := st108_p38
  have hstep := st108_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p40 : ((29956626056949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT108 (i+1))
      = (∑ i ∈ Finset.range 39, stT108 (i+1)) + stT108 40 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 39
    simpa using h
  have hprev := st108_p39
  have hstep := st108_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p41 : ((3145931846619/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT108 (i+1))
      = (∑ i ∈ Finset.range 40, stT108 (i+1)) + stT108 41 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 40
    simpa using h
  have hprev := st108_p40
  have hstep := st108_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p42 : ((1873088870503/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT108 (i+1))
      = (∑ i ∈ Finset.range 41, stT108 (i+1)) + stT108 42 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 41
    simpa using h
  have hprev := st108_p41
  have hstep := st108_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p43 : ((30960035409213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT108 (i+1))
      = (∑ i ∈ Finset.range 42, stT108 (i+1)) + stT108 43 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 42
    simpa using h
  have hprev := st108_p42
  have hstep := st108_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p44 : ((30887045529501/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT108 (i+1))
      = (∑ i ∈ Finset.range 43, stT108 (i+1)) + stT108 44 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 43
    simpa using h
  have hprev := st108_p43
  have hstep := st108_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p45 : ((29965778059941/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT108 (i+1))
      = (∑ i ∈ Finset.range 44, stT108 (i+1)) + stT108 45 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 44
    simpa using h
  have hprev := st108_p44
  have hstep := st108_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p46 : ((3928293848889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT108 (i+1))
      = (∑ i ∈ Finset.range 45, stT108 (i+1)) + stT108 46 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 45
    simpa using h
  have hprev := st108_p45
  have hstep := st108_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p47 : ((7573508221603/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT108 (i+1))
      = (∑ i ∈ Finset.range 46, stT108 (i+1)) + stT108 47 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 46
    simpa using h
  have hprev := st108_p46
  have hstep := st108_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p48 : ((7581007998103/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT108 (i+1))
      = (∑ i ∈ Finset.range 47, stT108 (i+1)) + stT108 48 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 47
    simpa using h
  have hprev := st108_p47
  have hstep := st108_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p49 : ((15718768686323/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT108 (i+1))
      = (∑ i ∈ Finset.range 48, stT108 (i+1)) + stT108 49 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 48
    simpa using h
  have hprev := st108_p48
  have hstep := st108_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p50 : ((3007941958517/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT108 (i+1))
      = (∑ i ∈ Finset.range 49, stT108 (i+1)) + stT108 50 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 49
    simpa using h
  have hprev := st108_p49
  have hstep := st108_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p51 : ((3047319652481/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT108 (i+1))
      = (∑ i ∈ Finset.range 50, stT108 (i+1)) + stT108 51 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 50
    simpa using h
  have hprev := st108_p50
  have hstep := st108_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p52 : ((3142781581031/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT108 (i+1))
      = (∑ i ∈ Finset.range 51, stT108 (i+1)) + stT108 52 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 51
    simpa using h
  have hprev := st108_p51
  have hstep := st108_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p53 : ((15052490517641/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT108 (i+1))
      = (∑ i ∈ Finset.range 52, stT108 (i+1)) + stT108 53 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 52
    simpa using h
  have hprev := st108_p52
  have hstep := st108_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p54 : ((30341888768539/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT108 (i+1))
      = (∑ i ∈ Finset.range 53, stT108 (i+1)) + stT108 54 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 53
    simpa using h
  have hprev := st108_p53
  have hstep := st108_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p55 : ((15732647629899/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT108 (i+1))
      = (∑ i ∈ Finset.range 54, stT108 (i+1)) + stT108 55 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 54
    simpa using h
  have hprev := st108_p54
  have hstep := st108_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p56 : ((3796207477889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT108 (i+1))
      = (∑ i ∈ Finset.range 55, stT108 (i+1)) + stT108 56 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 55
    simpa using h
  have hprev := st108_p55
  have hstep := st108_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p57 : ((600354257231/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT108 (i+1))
      = (∑ i ∈ Finset.range 56, stT108 (i+1)) + stT108 57 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 56
    simpa using h
  have hprev := st108_p56
  have hstep := st108_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p58 : ((15664865831303/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT108 (i+1))
      = (∑ i ∈ Finset.range 57, stT108 (i+1)) + stT108 58 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 57
    simpa using h
  have hprev := st108_p57
  have hstep := st108_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p59 : ((7731882417919/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT108 (i+1))
      = (∑ i ∈ Finset.range 58, stT108 (i+1)) + stT108 59 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 58
    simpa using h
  have hprev := st108_p58
  have hstep := st108_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p60 : ((29832563225461/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT108 (i+1))
      = (∑ i ∈ Finset.range 59, stT108 (i+1)) + stT108 60 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 59
    simpa using h
  have hprev := st108_p59
  have hstep := st108_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p61 : ((30726344593749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT108 (i+1))
      = (∑ i ∈ Finset.range 60, stT108 (i+1)) + stT108 61 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 60
    simpa using h
  have hprev := st108_p60
  have hstep := st108_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p62 : ((7864156094693/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT108 (i+1))
      = (∑ i ∈ Finset.range 61, stT108 (i+1)) + stT108 62 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 61
    simpa using h
  have hprev := st108_p61
  have hstep := st108_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p63 : ((7581277308997/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT108 (i+1))
      = (∑ i ∈ Finset.range 62, stT108 (i+1)) + stT108 63 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 62
    simpa using h
  have hprev := st108_p62
  have hstep := st108_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p64 : ((1197016206649/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT108 (i+1))
      = (∑ i ∈ Finset.range 63, stT108 (i+1)) + stT108 64 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 63
    simpa using h
  have hprev := st108_p63
  have hstep := st108_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p65 : ((15567656405249/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT108 (i+1))
      = (∑ i ∈ Finset.range 64, stT108 (i+1)) + stT108 65 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 64
    simpa using h
  have hprev := st108_p64
  have hstep := st108_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p66 : ((15655750458401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT108 (i+1))
      = (∑ i ∈ Finset.range 65, stT108 (i+1)) + stT108 66 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 65
    simpa using h
  have hprev := st108_p65
  have hstep := st108_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p67 : ((15047365895521/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT108 (i+1))
      = (∑ i ∈ Finset.range 66, stT108 (i+1)) + stT108 67 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 66
    simpa using h
  have hprev := st108_p66
  have hstep := st108_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p68 : ((30020558280007/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT108 (i+1))
      = (∑ i ∈ Finset.range 67, stT108 (i+1)) + stT108 68 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 67
    simpa using h
  have hprev := st108_p67
  have hstep := st108_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p69 : ((31222516592083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT108 (i+1))
      = (∑ i ∈ Finset.range 68, stT108 (i+1)) + stT108 69 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 68
    simpa using h
  have hprev := st108_p68
  have hstep := st108_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p70 : ((6261709581659/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT108 (i+1))
      = (∑ i ∈ Finset.range 69, stT108 (i+1)) + stT108 70 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 69
    simpa using h
  have hprev := st108_p69
  have hstep := st108_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p71 : ((30129002904931/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT108 (i+1))
      = (∑ i ∈ Finset.range 70, stT108 (i+1)) + stT108 71 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 70
    simpa using h
  have hprev := st108_p70
  have hstep := st108_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p72 : ((29928132605603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT108 (i+1))
      = (∑ i ∈ Finset.range 71, stT108 (i+1)) + stT108 72 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 71
    simpa using h
  have hprev := st108_p71
  have hstep := st108_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p73 : ((242667320299/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT108 (i+1))
      = (∑ i ∈ Finset.range 72, stT108 (i+1)) + stT108 73 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 72
    simpa using h
  have hprev := st108_p72
  have hstep := st108_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p74 : ((491625670091/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT108 (i+1))
      = (∑ i ∈ Finset.range 73, stT108 (i+1)) + stT108 74 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 73
    simpa using h
  have hprev := st108_p73
  have hstep := st108_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p75 : ((3043703565061/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT108 (i+1))
      = (∑ i ∈ Finset.range 74, stT108 (i+1)) + stT108 75 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 74
    simpa using h
  have hprev := st108_p74
  have hstep := st108_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p76 : ((5955003242389/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT108 (i+1))
      = (∑ i ∈ Finset.range 75, stT108 (i+1)) + stT108 76 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 75
    simpa using h
  have hprev := st108_p75
  have hstep := st108_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p77 : ((6117956273023/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT108 (i+1))
      = (∑ i ∈ Finset.range 76, stT108 (i+1)) + stT108 77 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 76
    simpa using h
  have hprev := st108_p76
  have hstep := st108_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p78 : ((31511654123867/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT108 (i+1))
      = (∑ i ∈ Finset.range 77, stT108 (i+1)) + stT108 78 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 77
    simpa using h
  have hprev := st108_p77
  have hstep := st108_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p79 : ((31048295631771/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT108 (i+1))
      = (∑ i ∈ Finset.range 78, stT108 (i+1)) + stT108 79 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 78
    simpa using h
  have hprev := st108_p78
  have hstep := st108_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p80 : ((5991053516043/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT108 (i+1))
      = (∑ i ∈ Finset.range 79, stT108 (i+1)) + stT108 80 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 79
    simpa using h
  have hprev := st108_p79
  have hstep := st108_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p81 : ((29936287565031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT108 (i+1))
      = (∑ i ∈ Finset.range 80, stT108 (i+1)) + stT108 81 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 80
    simpa using h
  have hprev := st108_p80
  have hstep := st108_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p82 : ((15501336328863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT108 (i+1))
      = (∑ i ∈ Finset.range 81, stT108 (i+1)) + stT108 82 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 81
    simpa using h
  have hprev := st108_p81
  have hstep := st108_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p83 : ((7888037786321/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT108 (i+1))
      = (∑ i ∈ Finset.range 82, stT108 (i+1)) + stT108 83 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 82
    simpa using h
  have hprev := st108_p82
  have hstep := st108_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p84 : ((15396635386517/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT108 (i+1))
      = (∑ i ∈ Finset.range 83, stT108 (i+1)) + stT108 84 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 83
    simpa using h
  have hprev := st108_p83
  have hstep := st108_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p85 : ((29829340736587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT108 (i+1))
      = (∑ i ∈ Finset.range 84, stT108 (i+1)) + stT108 85 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 84
    simpa using h
  have hprev := st108_p84
  have hstep := st108_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p86 : ((3751303158503/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT108 (i+1))
      = (∑ i ∈ Finset.range 85, stT108 (i+1)) + stT108 86 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 85
    simpa using h
  have hprev := st108_p85
  have hstep := st108_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p87 : ((3883735793303/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT108 (i+1))
      = (∑ i ∈ Finset.range 86, stT108 (i+1)) + stT108 87 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 86
    simpa using h
  have hprev := st108_p86
  have hstep := st108_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p88 : ((15785734237001/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT108 (i+1))
      = (∑ i ∈ Finset.range 87, stT108 (i+1)) + stT108 88 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 87
    simpa using h
  have hprev := st108_p87
  have hstep := st108_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p89 : ((617284247369/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT108 (i+1))
      = (∑ i ∈ Finset.range 88, stT108 (i+1)) + stT108 89 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 88
    simpa using h
  have hprev := st108_p88
  have hstep := st108_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p90 : ((29880006788443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT108 (i+1))
      = (∑ i ∈ Finset.range 89, stT108 (i+1)) + stT108 90 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 89
    simpa using h
  have hprev := st108_p89
  have hstep := st108_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p91 : ((3733541766871/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT108 (i+1))
      = (∑ i ∈ Finset.range 90, stT108 (i+1)) + stT108 91 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 90
    simpa using h
  have hprev := st108_p90
  have hstep := st108_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p92 : ((7706981696729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT108 (i+1))
      = (∑ i ∈ Finset.range 91, stT108 (i+1)) + stT108 92 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 91
    simpa using h
  have hprev := st108_p91
  have hstep := st108_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p93 : ((3157516819483/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT108 (i+1))
      = (∑ i ∈ Finset.range 92, stT108 (i+1)) + stT108 93 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 92
    simpa using h
  have hprev := st108_p92
  have hstep := st108_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p94 : ((3122112227911/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT108 (i+1))
      = (∑ i ∈ Finset.range 93, stT108 (i+1)) + stT108 94 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 93
    simpa using h
  have hprev := st108_p93
  have hstep := st108_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p95 : ((30198179150971/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT108 (i+1))
      = (∑ i ∈ Finset.range 94, stT108 (i+1)) + stT108 95 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 94
    simpa using h
  have hprev := st108_p94
  have hstep := st108_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p96 : ((29693224869979/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT108 (i+1))
      = (∑ i ∈ Finset.range 95, stT108 (i+1)) + stT108 96 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 95
    simpa using h
  have hprev := st108_p95
  have hstep := st108_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p97 : ((30267895475789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT108 (i+1))
      = (∑ i ∈ Finset.range 96, stT108 (i+1)) + stT108 97 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 96
    simpa using h
  have hprev := st108_p96
  have hstep := st108_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p98 : ((31268310620661/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT108 (i+1))
      = (∑ i ∈ Finset.range 97, stT108 (i+1)) + stT108 98 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 97
    simpa using h
  have hprev := st108_p97
  have hstep := st108_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p99 : ((31599393929349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT108 (i+1))
      = (∑ i ∈ Finset.range 98, stT108 (i+1)) + stT108 99 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 98
    simpa using h
  have hprev := st108_p98
  have hstep := st108_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st108_p100 : ((30917931929349/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT108 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT108 (i+1))
      = (∑ i ∈ Finset.range 99, stT108 (i+1)) + stT108 100 := by
    have h := Finset.sum_range_succ (fun i => stT108 (i+1)) 99
    simpa using h
  have hprev := st108_p99
  have hstep := st108_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 1600000 in
/-- **The certified detector sign at `t = 108`.** -/
theorem station_108_sign : 0 < hardyG (((108:ℕ)):ℝ) := by
  have hcore := phase_station_lower 108 100 (by norm_num) (by norm_num)
    ((-666873/500000 : ℚ) : ℝ)
  have hchain := st108_p100
  have hbridge : (∑ i ∈ Finset.range 100, stT108 (i+1))
      = ∑ i ∈ Finset.range 100,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos ((((108:ℕ)) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-666873/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_100
  have hsh := rpow_half_shifts (N := 100) (by norm_num)
  have hcost : ((100:ℕ):ℝ) ^ ((1/2:ℝ)) / (((108:ℕ)):ℝ)
      + ((100:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + ((((108:ℕ)):ℝ)+1) * ((((108:ℕ)):ℝ)+2) / 8
        * (((100:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((100:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((2498573/2160000 : ℚ) : ℝ) := by
    rw [hsh.1, hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((30917931929349/10000000000000 : ℚ) : ℝ) - ((2498573/2160000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp ((((-666873/500000 : ℚ)) : ℝ) * Complex.I)
      * riemannZeta (line (((108:ℕ)):ℝ))).re := by
    linarith [hcore, hchain, hcost, hm]
  have hP : 0 < Real.cos ((-666873/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((108:ℕ)):ℝ))).re
      - Real.sin ((-666873/500000 : ℚ) : ℝ)
        * (riemannZeta (line (((108:ℕ)):ℝ))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := (((108:ℕ)):ℝ)) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain (((108:ℕ)):ℝ)
      = ((((108:ℕ)):ℝ) * (Real.log (((108:ℕ)):ℝ) - Real.log 2
          - Real.log Real.pi) - (((108:ℕ)):ℝ)) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_108
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
  have hθwin : |(((-666873/500000 : ℚ) : ℝ) + ((16:ℤ)) * (2*Real.pi)) - theta (((108:ℕ)):ℝ)| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := (((108:ℕ)):ℝ))
    (φ := ((-666873/500000 : ℚ) : ℝ) + ((16:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-666873/500000 : ℚ)) : ℝ) 16).1,
    (cos_sin_shift (((-666873/500000 : ℚ)) : ℝ) 16).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_108_sign
end AxiomAudit
