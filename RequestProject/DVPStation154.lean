import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 154` (rung-154.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT154 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((154 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))

theorem st154_c1 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((191751/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 217699/1250000) (δ := 201/1000000000) (ψ := -696637/1000000) 154 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t1 : ((383477/500000 : ℚ) : ℝ) ≤ stT154 1 := by
  have hc : ((383477/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383477/500000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((383477/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c2 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((101213/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 156787/1000000) (δ := 489/62500000) (ψ := -696637/1000000) 154 17
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t2 : ((2862558840409/5000000000000 : ℚ) : ℝ) ≤ stT154 2 := by
  have hc : ((404827/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2862558840409/5000000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((404827/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c3 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((194413/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 592301/10000000) (δ := 1579/200000000) (ψ := -696637/1000000) 154 27
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t3 : ((561193054653/1000000000000 : ℚ) : ℝ) ≤ stT154 3 := by
  have hc : ((194403/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((561193054653/1000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((194403/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c4 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((212123/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 697083/5000000) (δ := 7757/1000000000) (ψ := -696637/1000000) 154 34
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t4 : ((424221/1000000 : ℚ) : ℝ) ≤ stT154 4 := by
  have hc : ((424221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((424221/1000000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((424221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c5 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-934387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6943327/10000000) (δ := 7889/1000000000) (ψ := -696637/1000000) 154 40
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t5 : ((-522366168429/1250000000000 : ℚ) : ℝ) ≤ stT154 5 := by
  have hc : ((-934437/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-522366168429/1250000000000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-934437/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c6 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((197203/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 418597/10000000) (δ := 7717/1000000000) (ψ := -696637/1000000) 154 44
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t6 : ((402518436513/1000000000000 : ℚ) : ℝ) ≤ stT154 6 := by
  have hc : ((197193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).1
  have hw2 : ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((402518436513/1000000000000 : ℚ) : ℝ)
      = ((2041241/5000000 : ℚ) : ℝ) * ((197193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c7 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((84479/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3065237/10000000) (δ := 7857/1000000000) (ψ := -696637/1000000) 154 48
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t7 : ((159626649963/1250000000000 : ℚ) : ℝ) ≤ stT154 7 := by
  have hc : ((168933/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159626649963/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((168933/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c8 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((176637/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1220463/10000000) (δ := 1967/250000000) (ψ := -696637/1000000) 154 51
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t8 : ((624470587191/2000000000000 : ℚ) : ℝ) ≤ stT154 8 := by
  have hc : ((176627/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((624470587191/2000000000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((176627/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c9 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((195057/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -139243/2500000) (δ := 7789/1000000000) (ψ := -696637/1000000) 154 54
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t9 : ((650156601651/2000000000000 : ℚ) : ℝ) ≤ stT154 9 := by
  have hc : ((195047/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((650156601651/2000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((195047/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c10 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-956871/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -711707/1000000) (δ := 1973/250000000) (ψ := -696637/1000000) 154 57
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t10 : ((-1513025113019/5000000000000 : ℚ) : ℝ) ≤ stT154 10 := by
  have hc : ((-956921/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).2
  have h0 : (0:ℝ) ≤ ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1513025113019/5000000000000 : ℚ) : ℝ)
      = ((1581139/5000000 : ℚ) : ℝ) * ((-956921/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c11 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((92693/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1838569/10000000) (δ := 309/40000000) (ψ := -696637/1000000) 154 59
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t11 : ((1117844099411/5000000000000 : ℚ) : ℝ) ≤ stT154 11 := by
  have hc : ((370747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).1
  have hw2 : ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3015113/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1117844099411/5000000000000 : ℚ) : ℝ)
      = ((3015113/10000000 : ℚ) : ℝ) * ((370747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c12 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((497603/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 244893/10000000) (δ := 983/125000000) (ψ := -696637/1000000) 154 61
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t12 : ((718191894539/2500000000000 : ℚ) : ℝ) ≤ stT154 12 := by
  have hc : ((248789/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((718191894539/2500000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((248789/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c13 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((494979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -177297/5000000) (δ := 7849/1000000000) (ψ := -696637/1000000) 154 63
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t13 : ((1372754919/5000000000 : ℚ) : ℝ) ≤ stT154 13 := by
  have hc : ((247477/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).1
  have hw2 : ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1372754919/5000000000 : ℚ) : ℝ)
      = ((5547/20000 : ℚ) : ℝ) * ((247477/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c14 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((271759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -161947/500000) (δ := 971/125000000) (ψ := -696637/1000000) 154 65
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t14 : ((181543183477/2500000000000 : ℚ) : ℝ) ≤ stT154 14 := by
  have hc : ((271709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((181543183477/2500000000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((271709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c15 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-124431/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7615363/10000000) (δ := 483/62500000) (ψ := -696637/1000000) 154 66
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t15 : ((-1285182442761/5000000000000 : ℚ) : ℝ) ≤ stT154 15 := by
  have hc : ((-497749/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1285182442761/5000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-497749/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c16 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((913617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1046759/10000000) (δ := 7713/1000000000) (ψ := -696637/1000000) 154 68
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t16 : ((913567/4000000 : ℚ) : ℝ) ≤ stT154 16 := by
  have hc : ((913567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((913567/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((913567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c17 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-189201/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7028697/10000000) (δ := 7899/1000000000) (ψ := -696637/1000000) 154 70
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t17 : ((-458904223327/2000000000000 : ℚ) : ℝ) ≤ stT154 17 := by
  have hc : ((-189211/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).2
  have h0 : (0:ℝ) ≤ ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-458904223327/2000000000000 : ℚ) : ℝ)
      = ((2425357/10000000 : ℚ) : ℝ) * ((-189211/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c18 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((119699/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -182669/2500000) (δ := 487/62500000) (ψ := -696637/1000000) 154 71
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t18 : ((564236889981/2500000000000 : ℚ) : ℝ) ≤ stT154 18 := by
  have hc : ((478771/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((564236889981/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((478771/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c19 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-1433/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4377233/10000000) (δ := 3859/500000000) (ψ := -696637/1000000) 154 72
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t19 : ((-8221115193/200000000000 : ℚ) : ℝ) ≤ stT154 19 := by
  have hc : ((-7167/40000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).2
  have h0 : (0:ℝ) ≤ ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-8221115193/200000000000 : ℚ) : ℝ)
      = ((1147079/5000000 : ℚ) : ℝ) * ((-7167/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c20 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-974731/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7290773/10000000) (δ := 7733/1000000000) (ψ := -696637/1000000) 154 74
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t20 : ((-544919150277/2500000000000 : ℚ) : ℝ) ≤ stT154 20 := by
  have hc : ((-974781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-544919150277/2500000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-974781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c21 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-57377/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4214509/10000000) (δ := 49/6250000) (ψ := -696637/1000000) 154 75
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t21 : ((-62630719479/2500000000000 : ℚ) : ℝ) ≤ stT154 21 := by
  have hc : ((-28701/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-62630719479/2500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-28701/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c22 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((693177/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2012273/10000000) (δ := 491/62500000) (ψ := -696637/1000000) 154 76
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t22 : ((1477751615889/10000000000000 : ℚ) : ℝ) ≤ stT154 22 := by
  have hc : ((693127/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1477751615889/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((693127/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c23 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((970737/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -606293/10000000) (δ := 7749/1000000000) (ψ := -696637/1000000) 154 77
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t23 : ((253002771741/1250000000000 : ℚ) : ℝ) ≤ stT154 23 := by
  have hc : ((970687/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253002771741/1250000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((970687/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c24 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((199919/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7119/1000000) (δ := 3881/500000000) (ψ := -696637/1000000) 154 78
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t24 : ((408062447069/2000000000000 : ℚ) : ℝ) ≤ stT154 24 := by
  have hc : ((199909/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).1
  have hw2 : ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2041241/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408062447069/2000000000000 : ℚ) : ℝ)
      = ((2041241/10000000 : ℚ) : ℝ) * ((199909/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c25 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((249873/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 79697/10000000) (δ := 7869/1000000000) (ψ := -696637/1000000) 154 79
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t25 : ((499721/2500000 : ℚ) : ℝ) ≤ stT154 25 := by
  have hc : ((499721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((499721/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((499721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c26 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((195551/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -528297/10000000) (δ := 243/31250000) (ψ := -696637/1000000) 154 80
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t26 : ((383487383101/2000000000000 : ℚ) : ℝ) ≤ stT154 26 := by
  have hc : ((195541/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((383487383101/2000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((195541/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c27 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((97/125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -341249/2000000) (δ := 193/25000000) (ψ := -696637/1000000) 154 81
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t27 : ((59732631/400000000 : ℚ) : ℝ) ≤ stT154 27 := by
  have hc : ((15519/20000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59732631/400000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((15519/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c28 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((20429/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -853161/2500000) (δ := 7813/1000000000) (ψ := -696637/1000000) 154 82
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t28 : ((2412357783/62500000000 : ℚ) : ℝ) ≤ stT154 28 := by
  have hc : ((2553/12500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2412357783/62500000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((2553/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c29 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-155909/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -701307/1250000) (δ := 7897/1000000000) (ψ := -696637/1000000) 154 83
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t29 : ((-289539053111/2500000000000 : ℚ) : ℝ) ≤ stT154 29 := by
  have hc : ((-311843/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).2
  have h0 : (0:ℝ) ≤ ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289539053111/2500000000000 : ℚ) : ℝ)
      = ((928477/5000000 : ℚ) : ℝ) * ((-311843/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c30 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-246607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7441621/10000000) (δ := 3853/500000000) (ψ := -696637/1000000) 154 83
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t30 : ((-450263579169/2500000000000 : ℚ) : ℝ) ≤ stT154 30 := by
  have hc : ((-493239/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-450263579169/2500000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-493239/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c31 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-8573/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4357769/10000000) (δ := 3899/500000000) (ψ := -696637/1000000) 154 84
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t31 : ((-15402061077/500000000000 : ℚ) : ℝ) ≤ stT154 31 := by
  have hc : ((-17151/100000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15402061077/500000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-17151/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c32 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((939639/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174611/2000000) (δ := 7891/1000000000) (ψ := -696637/1000000) 154 85
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t32 : ((830486744087/5000000000000 : ℚ) : ℝ) ≤ stT154 32 := by
  have hc : ((939589/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((830486744087/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((939589/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c33 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((183443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1493921/5000000) (δ := 973/125000000) (ψ := -696637/1000000) 154 86
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t33 : ((19955603273/312500000000 : ℚ) : ℝ) ≤ stT154 33 := by
  have hc : ((91709/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19955603273/312500000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((91709/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c34 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-966227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -9003/12500) (δ := 3863/500000000) (ψ := -696637/1000000) 154 87
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t34 : ((-828575763561/5000000000000 : ℚ) : ℝ) ≤ stT154 34 := by
  have hc : ((-966277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-828575763561/5000000000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-966277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c35 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-6159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3957787/10000000) (δ := 7877/1000000000) (ψ := -696637/1000000) 154 87
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t35 : ((-1306608857/625000000000 : ℚ) : ℝ) ≤ stT154 35 := by
  have hc : ((-773/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1306608857/625000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-773/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c36 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((467639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -904379/10000000) (δ := 7833/1000000000) (ψ := -696637/1000000) 154 88
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t36 : ((194839088731/1250000000000 : ℚ) : ℝ) ≤ stT154 36 := by
  have hc : ((233807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((194839088731/1250000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((233807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c37 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-754371/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -378983/625000) (δ := 7863/1000000000) (ψ := -696637/1000000) 154 89
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t37 : ((-124026057979/1000000000000 : ℚ) : ℝ) ≤ stT154 37 := by
  have hc : ((-754421/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).2
  have h0 : (0:ℝ) ≤ ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124026057979/1000000000000 : ℚ) : ℝ)
      = ((164399/1000000 : ℚ) : ℝ) * ((-754421/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c38 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-11039/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4203529/10000000) (δ := 7863/1000000000) (ψ := -696637/1000000) 154 89
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t38 : ((-895787123/50000000000 : ℚ) : ℝ) ≤ stT154 38 := by
  have hc : ((-2761/25000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-895787123/50000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-2761/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c39 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((824461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -751933/5000000) (δ := 981/125000000) (ψ := -696637/1000000) 154 90
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t39 : ((1320113670491/10000000000000 : ℚ) : ℝ) ≤ stT154 39 := by
  have hc : ((824411/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1320113670491/10000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((824411/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c40 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-987887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7464477/10000000) (δ := 981/125000000) (ψ := -696637/1000000) 154 91
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t40 : ((-1562065720243/10000000000000 : ℚ) : ℝ) ≤ stT154 40 := by
  have hc : ((-987937/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).2
  have h0 : (0:ℝ) ≤ ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1562065720243/10000000000000 : ℚ) : ℝ)
      = ((1581139/10000000 : ℚ) : ℝ) * ((-987937/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c41 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((684507/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1021087/5000000) (δ := 981/125000000) (ψ := -696637/1000000) 154 91
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t41 : ((1068941821809/10000000000000 : ℚ) : ℝ) ≤ stT154 41 := by
  have hc : ((684457/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).1
  have hw2 : ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1561737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1068941821809/10000000000000 : ℚ) : ℝ)
      = ((1561737/10000000 : ℚ) : ℝ) * ((684457/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c42 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-45861/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4388213/10000000) (δ := 7741/1000000000) (ψ := -696637/1000000) 154 92
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t42 : ((-70784370199/2500000000000 : ℚ) : ℝ) ≤ stT154 42 := by
  have hc : ((-91747/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-70784370199/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-91747/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c43 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-146621/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 467103/1000000) (δ := 3931/500000000) (ψ := -696637/1000000) 154 92
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t43 : ((-55908274239/1250000000000 : ℚ) : ℝ) ≤ stT154 43 := by
  have hc : ((-73323/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-55908274239/1250000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-73323/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c44 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((128293/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -273247/1250000) (δ := 7769/1000000000) (ψ := -696637/1000000) 154 93
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t44 : ((48348451587/500000000000 : ℚ) : ℝ) ≤ stT154 44 := by
  have hc : ((128283/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48348451587/500000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((128283/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c45 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-84981/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1616513/2500000) (δ := 7769/1000000000) (ψ := -696637/1000000) 154 93
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t45 : ((-7918103127/62500000000 : ℚ) : ℝ) ≤ stT154 45 := by
  have hc : ((-42493/50000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7918103127/62500000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-42493/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c46 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((951717/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -156007/2000000) (δ := 7727/1000000000) (ψ := -696637/1000000) 154 94
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t46 : ((1403155906473/10000000000000 : ℚ) : ℝ) ≤ stT154 46 := by
  have hc : ((951667/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1403155906473/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((951667/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c47 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-494993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7499891/10000000) (δ := 1969/250000000) (ψ := -696637/1000000) 154 94
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t47 : ((-7220580057/50000000000 : ℚ) : ℝ) ≤ stT154 47 := by
  have hc : ((-247509/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7220580057/50000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-247509/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c48 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((999159/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -51257/5000000) (δ := 7819/1000000000) (ψ := -696637/1000000) 154 95
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t48 : ((11536711623/80000000000 : ℚ) : ℝ) ≤ stT154 48 := by
  have hc : ((999109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11536711623/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((999109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c49 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-499987/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3917939/5000000) (δ := 7819/1000000000) (ψ := -696637/1000000) 154 95
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t49 : ((-44643946429/312500000000 : ℚ) : ℝ) ≤ stT154 49 := by
  have hc : ((-125003/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).2
  have h0 : (0:ℝ) ≤ ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-44643946429/312500000000 : ℚ) : ℝ)
      = ((357143/2500000 : ℚ) : ℝ) * ((-125003/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c50 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((999293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -94007/10000000) (δ := 241/31250000) (ψ := -696637/1000000) 154 96
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t50 : ((1413142440759/10000000000000 : ℚ) : ℝ) ≤ stT154 50 := by
  have hc : ((999243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1413142440759/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((999243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c51 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-495807/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3764997/5000000) (δ := 241/31250000) (ψ := -696637/1000000) 154 96
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t51 : ((-86788016099/625000000000 : ℚ) : ℝ) ≤ stT154 51 := by
  have hc : ((-61979/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-86788016099/625000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-61979/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c52 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((480417/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -702001/10000000) (δ := 1561/200000000) (ψ := -696637/1000000) 154 97
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t52 : ((333091803/2500000000 : ℚ) : ℝ) ≤ stT154 52 := by
  have hc : ((60049/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((333091803/2500000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((60049/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c53 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-882817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1657889/2500000) (δ := 1561/200000000) (ψ := -696637/1000000) 154 97
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t53 : ((-606355704201/5000000000000 : ℚ) : ℝ) ≤ stT154 53 := by
  have hc : ((-882867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).2
  have h0 : (0:ℝ) ≤ ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-606355704201/5000000000000 : ℚ) : ℝ)
      = ((686803/5000000 : ℚ) : ℝ) * ((-882867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c54 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((365169/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1879949/10000000) (δ := 3949/500000000) (ψ := -696637/1000000) 154 98
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t54 : ((62112226761/625000000000 : ℚ) : ℝ) ≤ stT154 54 := by
  have hc : ((45643/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).1
  have hw2 : ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1360827/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62112226761/625000000000 : ℚ) : ℝ)
      = ((1360827/10000000 : ℚ) : ℝ) * ((45643/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c55 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-120511/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1036891/2000000) (δ := 1541/200000000) (ψ := -696637/1000000) 154 98
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t55 : ((-812569437/12500000000 : ℚ) : ℝ) ≤ stT154 55 := by
  have hc : ((-241047/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-812569437/12500000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-241047/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c56 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((135821/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1793193/5000000) (δ := 7791/1000000000) (ψ := -696637/1000000) 154 99
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t56 : ((90715800963/5000000000000 : ℚ) : ℝ) ≤ stT154 56 := by
  have hc : ((135771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((90715800963/5000000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((135771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c57 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((275983/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 80699/250000) (δ := 7791/1000000000) (ψ := -696637/1000000) 154 99
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t57 : ((91370522089/2500000000000 : ℚ) : ℝ) ≤ stT154 57 := by
  have hc : ((275933/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((91370522089/2500000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((275933/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c58 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-676403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -36151/62500) (δ := 7719/1000000000) (ψ := -696637/1000000) 154 100
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t58 : ((-177645351689/2000000000000 : ℚ) : ℝ) ≤ stT154 58 := by
  have hc : ((-676453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-177645351689/2000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-676453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c59 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((949589/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6228/78125) (δ := 7719/1000000000) (ψ := -696637/1000000) 154 100
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t59 : ((1236194379171/10000000000000 : ℚ) : ℝ) ≤ stT154 59 := by
  have hc : ((949539/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1236194379171/10000000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((949539/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c60 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-121581/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7267917/10000000) (δ := 1971/250000000) (ψ := -696637/1000000) 154 100
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t60 : ((-125574825451/1000000000000 : ℚ) : ℝ) ≤ stT154 60 := by
  have hc : ((-486349/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-125574825451/1000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-486349/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c61 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((337251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -415253/2000000) (δ := 7827/1000000000) (ψ := -696637/1000000) 154 101
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t61 : ((13492918099/156250000000 : ℚ) : ℝ) ≤ stT154 61 := by
  have hc : ((168613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13492918099/156250000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((168613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c62 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-102633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4184027/10000000) (δ := 243/31250000) (ψ := -696637/1000000) 154 101
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t62 : ((-65203807683/5000000000000 : ℚ) : ℝ) ≤ stT154 62 := by
  have hc : ((-102683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-65203807683/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-102683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c63 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-543597/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2681891/5000000) (δ := 3867/500000000) (ψ := -696637/1000000) 154 102
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t63 : ((-342465534827/5000000000000 : ℚ) : ℝ) ≤ stT154 63 := by
  have hc : ((-543647/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).2
  have h0 : (0:ℝ) ≤ ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-342465534827/5000000000000 : ℚ) : ℝ)
      = ((629941/5000000 : ℚ) : ℝ) * ((-543647/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c64 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((961131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 699313/10000000) (δ := 7869/1000000000) (ψ := -696637/1000000) 154 102
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t64 : ((961081/8000000 : ℚ) : ℝ) ≤ stT154 64 := by
  have hc : ((961081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).1
  have hw2 : ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/8 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((961081/8000000 : ℚ) : ℝ)
      = ((1/8 : ℚ) : ℝ) * ((961081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c65 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-889649/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 666843/1000000) (δ := 7869/1000000000) (ψ := -696637/1000000) 154 102
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t65 : ((-275884093813/2500000000000 : ℚ) : ℝ) ≤ stT154 65 := by
  have hc : ((-889699/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-275884093813/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-889699/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c66 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((301417/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -632309/2000000) (δ := 7841/1000000000) (ψ := -696637/1000000) 154 103
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t66 : ((185478429719/5000000000000 : ℚ) : ℝ) ≤ stT154 66 := by
  have hc : ((301367/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185478429719/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((301367/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c67 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((248257/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1314023/5000000) (δ := 3881/500000000) (ψ := -696637/1000000) 154 103
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t67 : ((18953971563/312500000000 : ℚ) : ℝ) ≤ stT154 67 := by
  have hc : ((31029/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).1
  have hw2 : ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((610847/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18953971563/312500000000 : ℚ) : ℝ)
      = ((610847/5000000 : ℚ) : ℝ) * ((31029/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c68 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-490893/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922013/1250000) (δ := 1571/200000000) (ψ := -696637/1000000) 154 104
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t68 : ((-297662974661/2500000000000 : ℚ) : ℝ) ≤ stT154 68 := by
  have hc : ((-245459/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).2
  have h0 : (0:ℝ) ≤ ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-297662974661/2500000000000 : ℚ) : ℝ)
      = ((1212679/10000000 : ℚ) : ℝ) * ((-245459/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c69 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((381703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -877783/5000000) (δ := 1571/200000000) (ψ := -696637/1000000) 154 104
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t69 : ((114871528431/1250000000000 : ℚ) : ℝ) ≤ stT154 69 := by
  have hc : ((190839/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).1
  have hw2 : ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((601929/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((114871528431/1250000000000 : ℚ) : ℝ)
      = ((601929/5000000 : ℚ) : ℝ) * ((190839/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c70 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((14283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 946021/2500000) (δ := 1937/250000000) (ψ := -696637/1000000) 154 104
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t70 : ((8528250587/1250000000000 : ℚ) : ℝ) ≤ stT154 70 := by
  have hc : ((28541/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8528250587/1250000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((28541/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c71 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-6793/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -807851/1250000) (δ := 1571/200000000) (ψ := -696637/1000000) 154 105
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t71 : ((-20155712097/200000000000 : ℚ) : ℝ) ≤ stT154 71 := by
  have hc : ((-33967/40000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20155712097/200000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-33967/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c72 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((908451/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1078083/10000000) (δ := 1937/250000000) (ψ := -696637/1000000) 154 105
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t72 : ((1070560570911/10000000000000 : ℚ) : ℝ) ≤ stT154 72 := by
  have hc : ((908401/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1070560570911/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((908401/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c73 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-24367/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2116169/5000000) (δ := 1571/200000000) (ψ := -696637/1000000) 154 105
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t73 : ((-7132783331/500000000000 : ℚ) : ℝ) ≤ stT154 73 := by
  have hc : ((-24377/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7132783331/500000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-24377/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c74 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-399067/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -623747/1000000) (δ := 49/6250000) (ψ := -696637/1000000) 154 106
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t74 : ((-115983817721/1250000000000 : ℚ) : ℝ) ≤ stT154 74 := by
  have hc : ((-99773/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115983817721/1250000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-99773/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c75 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((227467/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -133697/1250000) (δ := 7763/1000000000) (ψ := -696637/1000000) 154 106
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t75 : ((5252834223/50000000000 : ℚ) : ℝ) ≤ stT154 75 := by
  have hc : ((454909/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5252834223/50000000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((454909/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c76 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-20561/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2014913/5000000) (δ := 7763/1000000000) (ψ := -696637/1000000) 154 106
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t76 : ((-11806884147/2500000000000 : ℚ) : ℝ) ≤ stT154 76 := by
  have hc : ((-10293/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).2
  have h0 : (0:ℝ) ≤ ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11806884147/2500000000000 : ℚ) : ℝ)
      = ((1147079/10000000 : ℚ) : ℝ) * ((-10293/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c77 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-885401/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6645379/10000000) (δ := 7733/1000000000) (ψ := -696637/1000000) 154 107
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t77 : ((-504532636153/5000000000000 : ℚ) : ℝ) ≤ stT154 77 := by
  have hc : ((-885451/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-504532636153/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-885451/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c78 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((783183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -167757/1000000) (δ := 7733/1000000000) (ψ := -696637/1000000) 154 107
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t78 : ((886723483841/10000000000000 : ℚ) : ℝ) ≤ stT154 78 := by
  have hc : ((783133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((886723483841/10000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((783133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c79 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((276373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 645389/2000000) (δ := 7733/1000000000) (ψ := -696637/1000000) 154 107
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t79 : ((310887415101/10000000000000 : ℚ) : ℝ) ≤ stT154 79 := by
  have hc : ((276323/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((310887415101/10000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((276323/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c80 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-996277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -381909/500000) (δ := 7777/1000000000) (ψ := -696637/1000000) 154 108
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t80 : ((-556963730559/5000000000000 : ℚ) : ℝ) ≤ stT154 80 := by
  have hc : ((-996327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-556963730559/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-996327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c81 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((103897/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1427759/5000000) (δ := 3913/500000000) (ψ := -696637/1000000) 154 108
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t81 : ((230854421359/5000000000000 : ℚ) : ℝ) ≤ stT154 81 := by
  have hc : ((207769/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((230854421359/5000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((207769/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c82 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((733467/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1868471/10000000) (δ := 7777/1000000000) (ψ := -696637/1000000) 154 108
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t82 : ((161984678871/2000000000000 : ℚ) : ℝ) ≤ stT154 82 := by
  have hc : ((733417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).1
  have hw2 : ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((220863/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161984678871/2000000000000 : ℚ) : ℝ)
      = ((220863/2000000 : ℚ) : ℝ) * ((733417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c83 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-13501/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 653521/1000000) (δ := 7777/1000000000) (ψ := -696637/1000000) 154 108
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t83 : ((-474244341651/5000000000000 : ℚ) : ℝ) ≤ stT154 83 := by
  have hc : ((-432057/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474244341651/5000000000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-432057/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c84 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-31407/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -285121/625000) (δ := 15519/1000000000) (ψ := -696637/1000000) 154 109
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t84 : ((-13709873177/500000000000 : ℚ) : ℝ) ≤ stT154 84 := by
  have hc : ((-125653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13709873177/500000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-125653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c85 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((999997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -709/1250000) (δ := 1971/250000000) (ψ := -696637/1000000) 154 109
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t85 : ((271148628361/2500000000000 : ℚ) : ℝ) ≤ stT154 85 := by
  have hc : ((999947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((271148628361/2500000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((999947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c86 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-113073/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 562161/1250000) (δ := 1971/250000000) (ψ := -696637/1000000) 154 109
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t86 : ((-7622296259/312500000000 : ℚ) : ℝ) ≤ stT154 86 := by
  have hc : ((-56549/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7622296259/312500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-56549/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c87 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-14152/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6759729/10000000) (δ := 7791/1000000000) (ψ := -696637/1000000) 154 110
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t87 : ((-485548184457/5000000000000 : ℚ) : ℝ) ≤ stT154 87 := by
  have hc : ((-452889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485548184457/5000000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-452889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c88 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((586657/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3687/15625) (δ := 1953/250000000) (ψ := -696637/1000000) 154 110
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t88 : ((625324821821/10000000000000 : ℚ) : ℝ) ≤ stT154 88 := by
  have hc : ((586607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((625324821821/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((586607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c89 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((699391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 497657/2500000) (δ := 7791/1000000000) (ψ := -696637/1000000) 154 110
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t89 : ((741299361977/10000000000000 : ℚ) : ℝ) ≤ stT154 89 := by
  have hc : ((699341/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).1
  have hw2 : ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1059997/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((741299361977/10000000000000 : ℚ) : ℝ)
      = ((1059997/10000000 : ℚ) : ℝ) * ((699341/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c90 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-405583/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1573087/2500000) (δ := 1953/250000000) (ψ := -696637/1000000) 154 110
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t90 : ((-53443569193/625000000000 : ℚ) : ℝ) ≤ stT154 90 := by
  have hc : ((-50701/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).2
  have h0 : (0:ℝ) ≤ ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53443569193/625000000000 : ℚ) : ℝ)
      = ((1054093/10000000 : ℚ) : ℝ) * ((-50701/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c91 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-473951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5161423/10000000) (δ := 3101/200000000) (ψ := -696637/1000000) 154 111
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t91 : ((-99377627657/2000000000000 : ℚ) : ℝ) ≤ stT154 91 := by
  have hc : ((-474001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99377627657/2000000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-474001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c92 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((928109/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -476869/5000000) (δ := 3949/500000000) (ψ := -696637/1000000) 154 111
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t92 : ((241892081937/2500000000000 : ℚ) : ℝ) ≤ stT154 92 := by
  have hc : ((928059/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((241892081937/2500000000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((928059/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c93 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((17717/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1604229/5000000) (δ := 1541/200000000) (ψ := -696637/1000000) 154 111
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t93 : ((146947363161/5000000000000 : ℚ) : ℝ) ≤ stT154 93 := by
  have hc : ((141711/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146947363161/5000000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((141711/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c94 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-488897/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7326149/10000000) (δ := 3949/500000000) (ψ := -696637/1000000) 154 111
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t94 : ((-126071226771/1250000000000 : ℚ) : ℝ) ≤ stT154 94 := by
  have hc : ((-244461/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126071226771/1250000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-244461/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c95 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-75849/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2153853/5000000) (δ := 3903/500000000) (ψ := -696637/1000000) 154 112
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t95 : ((-38922565323/2500000000000 : ℚ) : ℝ) ≤ stT154 95 := by
  have hc : ((-37937/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-38922565323/2500000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-37937/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c96 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((993901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -8633/312500) (δ := 7797/1000000000) (ψ := -696637/1000000) 154 112
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t96 : ((50717210381/500000000000 : ℚ) : ℝ) ≤ stT154 96 := by
  have hc : ((993851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).1
  have hw2 : ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50717210381/500000000000 : ℚ) : ℝ)
      = ((51031/500000 : ℚ) : ℝ) * ((993851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c97 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((21331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1856711/5000000) (δ := 7797/1000000000) (ψ := -696637/1000000) 154 112
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t97 : ((21645653701/2500000000000 : ℚ) : ℝ) ≤ stT154 97 := by
  have hc : ((42637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21645653701/2500000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((42637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c98 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-498529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 306487/400000) (δ := 3903/500000000) (ψ := -696637/1000000) 154 112
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t98 : ((-251807909381/2500000000000 : ℚ) : ℝ) ≤ stT154 98 := by
  have hc : ((-249277/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251807909381/2500000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-249277/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c99 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-83951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -827423/2000000) (δ := 789/100000000) (ψ := -696637/1000000) 154 113
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t99 : ((-42212098519/5000000000000 : ℚ) : ℝ) ≤ stT154 99 := by
  have hc : ((-84001/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42212098519/5000000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-84001/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c100 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((99427/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -267749/10000000) (δ := 7713/1000000000) (ψ := -696637/1000000) 154 113
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t100 : ((49710950289/500000000000 : ℚ) : ℝ) ≤ stT154 100 := by
  have hc : ((49711/50000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49710950289/500000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((49711/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c101 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((145021/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 712631/2000000) (δ := 7713/1000000000) (ψ := -696637/1000000) 154 113
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t101 : ((144251508927/10000000000000 : ℚ) : ℝ) ≤ stT154 101 := by
  have hc : ((144971/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((144251508927/10000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((144971/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c102 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-3921/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 735629/1000000) (δ := 789/100000000) (ψ := -696637/1000000) 154 113
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t102 : ((-2426605211/25000000000 : ℚ) : ℝ) ≤ stT154 102 := by
  have hc : ((-9803/10000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2426605211/25000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-9803/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c103 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-264257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2297787/5000000) (δ := 391/50000000) (ψ := -696637/1000000) 154 114
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t103 : ((-26042961631/1000000000000 : ℚ) : ℝ) ≤ stT154 103 := by
  have hc : ((-264307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26042961631/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-264307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c104 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((939271/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -875743/10000000) (δ := 7783/1000000000) (ψ := -696637/1000000) 154 114
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t104 : ((46049066409/500000000000 : ℚ) : ℝ) ≤ stT154 104 := by
  have hc : ((939221/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46049066409/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((939221/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c105 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((216307/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 561703/2000000) (δ := 391/50000000) (ψ := -696637/1000000) 154 114
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t105 : ((1055348019/25000000000 : ℚ) : ℝ) ≤ stT154 105 := by
  have hc : ((108141/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1055348019/25000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((108141/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c106 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-212017/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3228907/5000000) (δ := 7783/1000000000) (ψ := -696637/1000000) 154 114
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t106 : ((-205941284937/2500000000000 : ℚ) : ℝ) ≤ stT154 106 := by
  have hc : ((-424059/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-205941284937/2500000000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-424059/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c107 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-78913/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1408769/2500000) (δ := 7727/1000000000) (ψ := -696637/1000000) 154 115
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t107 : ((-305176635949/5000000000000 : ℚ) : ℝ) ≤ stT154 107 := by
  have hc : ((-315677/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).2
  have h0 : (0:ℝ) ≤ ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305176635949/5000000000000 : ℚ) : ℝ)
      = ((966737/10000000 : ℚ) : ℝ) * ((-315677/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c108 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((10643/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -513413/2500000) (δ := 7727/1000000000) (ψ := -696637/1000000) 154 115
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t108 : ((1310780799/20000000000 : ℚ) : ℝ) ≤ stT154 108 := by
  have hc : ((340551/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1310780799/20000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((340551/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c109 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((413261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1494739/10000000) (δ := 7727/1000000000) (ψ := -696637/1000000) 154 115
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t109 : ((49476023117/625000000000 : ℚ) : ℝ) ≤ stT154 109 := by
  have hc : ((103309/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49476023117/625000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((103309/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c110 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-420053/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5010751/10000000) (δ := 1969/250000000) (ψ := -696637/1000000) 154 115
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t110 : ((-400552666689/10000000000000 : ℚ) : ℝ) ≤ stT154 110 := by
  have hc : ((-420103/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-400552666689/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-420103/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c111 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-967311/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7213/10000) (δ := 3917/500000000) (ψ := -696637/1000000) 154 116
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t111 : ((-459089216019/5000000000000 : ℚ) : ℝ) ≤ stT154 111 := by
  have hc : ((-967361/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459089216019/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-967361/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c112 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((66711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3760089/10000000) (δ := 3917/500000000) (ψ := -696637/1000000) 154 116
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t112 : ((62988712171/10000000000000 : ℚ) : ℝ) ≤ stT154 112 := by
  have hc : ((66661/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62988712171/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((66661/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c113 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((247721/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -10557/312500) (δ := 3917/500000000) (ψ := -696637/1000000) 154 116
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t113 : ((5825608503/62500000000 : ℚ) : ℝ) ≤ stT154 113 := by
  have hc : ((495417/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5825608503/62500000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((495417/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c114 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((171023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3054257/10000000) (δ := 3917/500000000) (ψ := -696637/1000000) 154 116
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t114 : ((16015416183/500000000000 : ℚ) : ℝ) ≤ stT154 114 := by
  have hc : ((85499/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).1
  have hw2 : ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((187317/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16015416183/500000000000 : ℚ) : ℝ)
      = ((187317/2000000 : ℚ) : ℝ) * ((85499/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c115 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-839247/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6416731/10000000) (δ := 7769/1000000000) (ψ := -696637/1000000) 154 116
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t115 : ((-156529729797/2000000000000 : ℚ) : ℝ) ≤ stT154 115 := by
  have hc : ((-839297/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).2
  have h0 : (0:ℝ) ≤ ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-156529729797/2000000000000 : ℚ) : ℝ)
      = ((186501/2000000 : ℚ) : ℝ) * ((-839297/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c116 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-145183/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2978951/5000000) (δ := 3871/500000000) (ψ := -696637/1000000) 154 117
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t116 : ((-134808361061/2000000000000 : ℚ) : ℝ) ≤ stT154 116 := by
  have hc : ((-145193/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).2
  have h0 : (0:ℝ) ≤ ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134808361061/2000000000000 : ℚ) : ℝ)
      = ((928477/10000000 : ℚ) : ℝ) * ((-145193/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c117 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((15243/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2653139/10000000) (δ := 3871/500000000) (ψ := -696637/1000000) 154 117
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t117 : ((450902687/10000000000 : ℚ) : ℝ) ≤ stT154 117 := by
  have hc : ((243863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).1
  have hw2 : ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((450902687/10000000000 : ℚ) : ℝ)
      = ((1849/20000 : ℚ) : ℝ) * ((243863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c118 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((969063/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 15587/250000) (δ := 7861/1000000000) (ψ := -696637/1000000) 154 117
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t118 : ((446024086731/5000000000000 : ℚ) : ℝ) ≤ stT154 118 := by
  have hc : ((969013/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).1
  have hw2 : ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((460287/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((446024086731/5000000000000 : ℚ) : ℝ)
      = ((460287/5000000 : ℚ) : ℝ) * ((969013/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c119 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((21827/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1936209/5000000) (δ := 7861/1000000000) (ψ := -696637/1000000) 154 117
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t119 : ((9981466173/5000000000000 : ℚ) : ℝ) ≤ stT154 119 := by
  have hc : ((21777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9981466173/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((21777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c120 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-38167/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3547107/5000000) (δ := 3871/500000000) (ψ := -696637/1000000) 154 117
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t120 : ((-34843373199/400000000000 : ℚ) : ℝ) ≤ stT154 120 := by
  have hc : ((-38169/40000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34843373199/400000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-38169/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c121 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-280953/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5418711/10000000) (δ := 7849/1000000000) (ψ := -696637/1000000) 154 118
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t121 : ((-127717285499/2500000000000 : ℚ) : ℝ) ≤ stT154 121 := by
  have hc : ((-140489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-127717285499/2500000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-140489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c122 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((31081/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2249969/10000000) (δ := 3877/500000000) (ψ := -696637/1000000) 154 118
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t122 : ((56274275049/1000000000000 : ℚ) : ℝ) ≤ stT154 122 := by
  have hc : ((62157/100000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((56274275049/1000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((62157/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c123 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((936893/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 446451/5000000) (δ := 7849/1000000000) (ψ := -696637/1000000) 154 118
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t123 : ((844722290967/10000000000000 : ℚ) : ℝ) ≤ stT154 123 := by
  have hc : ((936843/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((844722290967/10000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((936843/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c124 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-33327/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1002581/2500000) (δ := 7849/1000000000) (ψ := -696637/1000000) 154 118
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t124 : ((-29973447179/10000000000000 : ℚ) : ℝ) ≤ stT154 124 := by
  have hc : ((-33377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29973447179/10000000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-33377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c125 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-955187/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7102721/10000000) (δ := 7849/1000000000) (ψ := -696637/1000000) 154 118
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t125 : ((-213597679859/2500000000000 : ℚ) : ℝ) ≤ stT154 125 := by
  have hc : ((-955237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).2
  have h0 : (0:ℝ) ≤ ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-213597679859/2500000000000 : ℚ) : ℝ)
      = ((223607/2500000 : ℚ) : ℝ) * ((-955237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c126 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-600557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2768743/5000000) (δ := 7847/1000000000) (ψ := -696637/1000000) 154 119
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t126 : ((-535063358697/10000000000000 : ℚ) : ℝ) ≤ stT154 126 := by
  have hc : ((-600607/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-535063358697/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-600607/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c127 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((542313/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1247011/5000000) (δ := 1939/250000000) (ψ := -696637/1000000) 154 119
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t127 : ((120295081657/2500000000000 : ℚ) : ℝ) ≤ stT154 127 := by
  have hc : ((542263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).1
  have hw2 : ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((221839/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((120295081657/2500000000000 : ℚ) : ℝ)
      = ((221839/2500000 : ℚ) : ℝ) * ((542263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c128 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((48899/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 52561/1000000) (δ := 1939/250000000) (ψ := -696637/1000000) 154 119
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t128 : ((86437570219/1000000000000 : ℚ) : ℝ) ≤ stT154 128 := by
  have hc : ((97793/100000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86437570219/1000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((97793/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c129 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((32277/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3521757/10000000) (δ := 1939/250000000) (ψ := -696637/1000000) 154 119
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t129 : ((568189603/40000000000 : ℚ) : ℝ) ≤ stT154 129 := by
  have hc : ((32267/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568189603/40000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((32267/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c130 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-4279/5000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6494727/10000000) (δ := 1939/250000000) (ψ := -696637/1000000) 154 119
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t130 : ((-15012618903/200000000000 : ℚ) : ℝ) ≤ stT154 130 := by
  have hc : ((-17117/20000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).2
  have h0 : (0:ℝ) ≤ ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15012618903/200000000000 : ℚ) : ℝ)
      = ((877059/10000000 : ℚ) : ℝ) * ((-17117/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c131 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-3217/4000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313151/500000) (δ := 387/50000000) (ψ := -696637/1000000) 154 120
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t131 : ((-1405441863/20000000000 : ℚ) : ℝ) ≤ stT154 131 := by
  have hc : ((-8043/10000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1405441863/20000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-8043/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c132 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((234493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3335249/10000000) (δ := 387/50000000) (ψ := -696637/1000000) 154 120
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t132 : ((51014093471/2500000000000 : ℚ) : ℝ) ≤ stT154 132 := by
  have hc : ((234443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).1
  have hw2 : ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((51014093471/2500000000000 : ℚ) : ℝ)
      = ((217597/2500000 : ℚ) : ℝ) * ((234443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c133 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((985273/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -429577/10000000) (δ := 387/50000000) (ψ := -696637/1000000) 154 120
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t133 : ((854295730307/10000000000000 : ℚ) : ℝ) ≤ stT154 133 := by
  have hc : ((985223/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((854295730307/10000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((985223/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c134 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((277793/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2454323/10000000) (δ := 777/50000000) (ψ := -696637/1000000) 154 120
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t134 : ((7498590207/156250000000 : ℚ) : ℝ) ≤ stT154 134 := by
  have hc : ((34721/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7498590207/156250000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((34721/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c135 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-527721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5316779/10000000) (δ := 387/50000000) (ψ := -696637/1000000) 154 120
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t135 : ((-454232972173/10000000000000 : ℚ) : ℝ) ≤ stT154 135 := by
  have hc : ((-527771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-454232972173/10000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-527771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c136 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-992609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3774923/5000000) (δ := 7833/1000000000) (ψ := -696637/1000000) 154 121
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t136 : ((-851198143887/10000000000000 : ℚ) : ℝ) ≤ stT154 136 := by
  have hc : ((-992659/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-851198143887/10000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-992659/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c137 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-157721/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4729297/10000000) (δ := 777/100000000) (ψ := -696637/1000000) 154 121
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t137 : ((-33692889267/1250000000000 : ℚ) : ℝ) ≤ stT154 137 := by
  have hc : ((-78873/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33692889267/1250000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-78873/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c138 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((71671/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -482327/2500000) (δ := 7833/1000000000) (ψ := -696637/1000000) 154 121
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t138 : ((3812882031/62500000000 : ℚ) : ℝ) ≤ stT154 138 := by
  have hc : ((35833/50000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3812882031/62500000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((35833/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c139 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((942687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 212627/2500000) (δ := 777/100000000) (ψ := -696637/1000000) 154 121
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t139 : ((199883347939/2500000000000 : ℚ) : ℝ) ≤ stT154 139 := by
  have hc : ((942637/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((199883347939/2500000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((942637/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c140 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((63153/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 180519/500000) (δ := 7833/1000000000) (ψ := -696637/1000000) 154 121
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t140 : ((3334555107/312500000000 : ℚ) : ℝ) ≤ stT154 140 := by
  have hc : ((7891/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3334555107/312500000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((7891/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c141 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-412283/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6350579/10000000) (δ := 7833/1000000000) (ψ := -696637/1000000) 154 121
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t141 : ((-10850812713/156250000000 : ℚ) : ℝ) ≤ stT154 141 := by
  have hc : ((-103077/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-10850812713/156250000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-103077/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c142 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-441873/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -207391/312500) (δ := 3863/500000000) (ψ := -696637/1000000) 154 122
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t142 : ((-92708211859/1250000000000 : ℚ) : ℝ) ≤ stT154 142 := by
  have hc : ((-220949/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92708211859/1250000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-220949/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c143 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-1549/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -245921/625000) (δ := 3863/500000000) (ψ := -696637/1000000) 154 122
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t143 : ((-658123241/2500000000000 : ℚ) : ℝ) ≤ stT154 143 := by
  have hc : ((-787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-658123241/2500000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c144 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((54827/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -50073/400000) (δ := 3863/500000000) (ψ := -696637/1000000) 154 122
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t144 : ((365492353803/5000000000000 : ℚ) : ℝ) ≤ stT154 144 := by
  have hc : ((438591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((365492353803/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((438591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c145 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((422287/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 176571/1250000) (δ := 7877/1000000000) (ψ := -696637/1000000) 154 122
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t145 : ((87667291737/1250000000000 : ℚ) : ℝ) ≤ stT154 145 := by
  have hc : ((211131/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87667291737/1250000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((211131/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c146 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-52633/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2029317/5000000) (δ := 3863/500000000) (ψ := -696637/1000000) 154 122
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t146 : ((-21800383449/5000000000000 : ℚ) : ℝ) ≤ stT154 146 := by
  have hc : ((-52683/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21800383449/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-52683/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c147 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-178589/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3343303/5000000) (δ := 7877/1000000000) (ψ := -696637/1000000) 154 122
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t147 : ((-147306133413/2000000000000 : ℚ) : ℝ) ≤ stT154 147 := by
  have hc : ((-178599/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147306133413/2000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-178599/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c148 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-209509/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6411173/10000000) (δ := 1557/200000000) (ψ := -696637/1000000) 154 123
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t148 : ((-68890250157/1000000000000 : ℚ) : ℝ) ≤ stT154 148 := by
  have hc : ((-419043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).2
  have h0 : (0:ℝ) ≤ ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68890250157/1000000000000 : ℚ) : ℝ)
      = ((164399/2000000 : ℚ) : ℝ) * ((-419043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c149 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((8673/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -763709/2000000) (δ := 3909/500000000) (ψ := -696637/1000000) 154 123
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t149 : ((7096998153/2000000000000 : ℚ) : ℝ) ≤ stT154 149 := by
  have hc : ((8663/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7096998153/2000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((8663/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c150 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((878861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -621659/5000000) (δ := 1557/200000000) (ψ := -696637/1000000) 154 123
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t150 : ((44846604141/625000000000 : ℚ) : ℝ) ≤ stT154 150 := by
  have hc : ((878811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).1
  have hw2 : ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((51031/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44846604141/625000000000 : ℚ) : ℝ)
      = ((51031/625000 : ℚ) : ℝ) * ((878811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c151 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((216213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1314853/10000000) (δ := 1557/200000000) (ψ := -696637/1000000) 154 123
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t151 : ((87970686247/1250000000000 : ℚ) : ℝ) ≤ stT154 151 := by
  have hc : ((432401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).1
  have hw2 : ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((203447/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87970686247/1250000000000 : ℚ) : ℝ)
      = ((203447/2500000 : ℚ) : ℝ) * ((432401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c152 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((3543/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1928061/5000000) (δ := 3909/500000000) (ψ := -696637/1000000) 154 123
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t152 : ((11474730729/5000000000000 : ℚ) : ℝ) ≤ stT154 152 := by
  have hc : ((14147/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11474730729/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((14147/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c153 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-25979/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6380721/10000000) (δ := 3909/500000000) (ψ := -696637/1000000) 154 123
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t153 : ((-336065019117/5000000000000 : ℚ) : ℝ) ≤ stT154 153 := by
  have hc : ((-415689/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).2
  have h0 : (0:ℝ) ≤ ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-336065019117/5000000000000 : ℚ) : ℝ)
      = ((808453/10000000 : ℚ) : ℝ) * ((-415689/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c154 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-183107/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3409541/5000000) (δ := 1973/250000000) (ψ := -696637/1000000) 154 124
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t154 : ((-147559890291/2000000000000 : ℚ) : ℝ) ≤ stT154 154 := by
  have hc : ((-183117/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-147559890291/2000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-183117/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c155 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-159389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -432717/1000000) (δ := 7711/1000000000) (ψ := -696637/1000000) 154 124
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t155 : ((-6403229679/500000000000 : ℚ) : ℝ) ≤ stT154 155 := by
  have hc : ((-159439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6403229679/500000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-159439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c156 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((1181/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1851273/10000000) (δ := 1973/250000000) (ψ := -696637/1000000) 154 124
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t156 : ((36933273/625000000 : ℚ) : ℝ) ≤ stT154 156 := by
  have hc : ((29523/40000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36933273/625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((29523/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c157 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((194099/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 761/12500) (δ := 1973/250000000) (ψ := -696637/1000000) 154 124
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t157 : ((77449856827/1000000000000 : ℚ) : ℝ) ≤ stT154 157 := by
  have hc : ((194089/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((77449856827/1000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((194089/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c158 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((85607/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1526621/5000000) (δ := 1973/250000000) (ψ := -696637/1000000) 154 124
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t158 : ((136190607273/5000000000000 : ℚ) : ℝ) ≤ stT154 158 := by
  have hc : ((171189/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((136190607273/5000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((171189/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c159 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-582757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1370571/2500000) (δ := 1973/250000000) (ψ := -696637/1000000) 154 124
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t159 : ((-115549064241/2500000000000 : ℚ) : ℝ) ≤ stT154 159 := by
  have hc : ((-582807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115549064241/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-582807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c160 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-499929/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1952971/2500000) (δ := 1951/250000000) (ψ := -696637/1000000) 154 125
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t160 : ((-19762431689/250000000000 : ℚ) : ℝ) ≤ stT154 160 := by
  have hc : ((-249977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19762431689/250000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-249977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c161 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-280031/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5413141/10000000) (δ := 7799/1000000000) (ψ := -696637/1000000) 154 125
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t161 : ((-27589401777/625000000000 : ℚ) : ℝ) ≤ stT154 161 := by
  have hc : ((-35007/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-27589401777/625000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-35007/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c162 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((351439/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3029221/10000000) (δ := 7799/1000000000) (ψ := -696637/1000000) 154 125
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t162 : ((138038600593/5000000000000 : ℚ) : ℝ) ≤ stT154 162 := by
  have hc : ((351389/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138038600593/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((351389/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c163 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((965357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -65997/1000000) (δ := 1951/250000000) (ψ := -696637/1000000) 154 125
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t163 : ((37804318041/500000000000 : ℚ) : ℝ) ≤ stT154 163 := by
  have hc : ((965307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).1
  have hw2 : ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((39163/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((37804318041/500000000000 : ℚ) : ℝ)
      = ((39163/500000 : ℚ) : ℝ) * ((965307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c164 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((778887/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1694767/10000000) (δ := 1951/250000000) (ψ := -696637/1000000) 154 125
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t164 : ((152042222629/2500000000000 : ℚ) : ℝ) ≤ stT154 164 := by
  have hc : ((778837/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((152042222629/2500000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((778837/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c165 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-43263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2017591/5000000) (δ := 1951/250000000) (ψ := -696637/1000000) 154 125
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t165 : ((-33719127187/10000000000000 : ℚ) : ℝ) ≤ stT154 165 := by
  have hc : ((-43313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).2
  have h0 : (0:ℝ) ≤ ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33719127187/10000000000000 : ℚ) : ℝ)
      = ((778499/10000000 : ℚ) : ℝ) * ((-43313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c166 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-827023/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1590367/2500000) (δ := 7799/1000000000) (ψ := -696637/1000000) 154 125
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t166 : ((-641933536023/10000000000000 : ℚ) : ℝ) ≤ stT154 166 := by
  have hc : ((-827073/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).2
  have h0 : (0:ℝ) ≤ ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-641933536023/10000000000000 : ℚ) : ℝ)
      = ((776151/10000000 : ℚ) : ℝ) * ((-827073/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c167 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-94671/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7034147/10000000) (δ := 3853/500000000) (ψ := -696637/1000000) 154 126
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t167 : ((-286181879/3906250000 : ℚ) : ℝ) ≤ stT154 167 := by
  have hc : ((-23669/25000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286181879/3906250000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-23669/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c168 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-9933/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4735659/10000000) (δ := 7897/1000000000) (ψ := -696637/1000000) 154 126
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t168 : ((-122634941701/5000000000000 : ℚ) : ℝ) ≤ stT154 168 := by
  have hc : ((-158953/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122634941701/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-158953/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c169 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((55677/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2450761/10000000) (δ := 7897/1000000000) (ψ := -696637/1000000) 154 126
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t169 : ((535307157/12500000000 : ℚ) : ℝ) ≤ stT154 169 := by
  have hc : ((6959/12500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).1
  have hw2 : ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((76923/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((535307157/12500000000 : ℚ) : ℝ)
      = ((76923/1000000 : ℚ) : ℝ) * ((6959/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c170 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((997427/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -11211/625000) (δ := 3853/500000000) (ψ := -696637/1000000) 154 126
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t170 : ((191238063357/2500000000000 : ℚ) : ℝ) ≤ stT154 170 := by
  have hc : ((997377/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((191238063357/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((997377/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c171 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((673787/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2078687/10000000) (δ := 7897/1000000000) (ψ := -696637/1000000) 154 126
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t171 : ((515219484903/10000000000000 : ℚ) : ℝ) ≤ stT154 171 := by
  have hc : ((673737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((515219484903/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((673737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c172 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-157973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 33778/78125) (δ := 3853/500000000) (ψ := -696637/1000000) 154 126
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t172 : ((-120491431339/10000000000000 : ℚ) : ℝ) ≤ stT154 172 := by
  have hc : ((-158023/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-120491431339/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-158023/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c173 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-434057/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6555467/10000000) (δ := 7897/1000000000) (ψ := -696637/1000000) 154 126
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t173 : ((-82506616863/1250000000000 : ℚ) : ℝ) ≤ stT154 173 := by
  have hc : ((-217041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-82506616863/1250000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-217041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c174 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-37319/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6933471/10000000) (δ := 7813/1000000000) (ψ := -696637/1000000) 154 127
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t174 : ((-28293012779/400000000000 : ℚ) : ℝ) ≤ stT154 174 := by
  have hc : ((-37321/40000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28293012779/400000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-37321/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c175 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-78657/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -295447/625000) (δ := 779/100000000) (ψ := -696637/1000000) 154 127
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t175 : ((-118937112931/5000000000000 : ℚ) : ℝ) ≤ stT154 175 := by
  have hc : ((-157339/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-118937112931/5000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-157339/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c176 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((105801/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1266711/5000000) (δ := 779/100000000) (ψ := -696637/1000000) 154 127
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t176 : ((39871464199/1000000000000 : ℚ) : ℝ) ≤ stT154 176 := by
  have hc : ((105791/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39871464199/1000000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((105791/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c177 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((990099/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -352089/10000000) (δ := 779/100000000) (ψ := -696637/1000000) 154 127
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t177 : ((372083185327/5000000000000 : ℚ) : ℝ) ≤ stT154 177 := by
  have hc : ((990049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((372083185327/5000000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((990049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c178 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((29893/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 454231/2500000) (δ := 779/100000000) (ψ := -696637/1000000) 154 127
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t178 : ((22404231121/400000000000 : ℚ) : ℝ) ≤ stT154 178 := by
  have hc : ((29891/40000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((22404231121/400000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((29891/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c179 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-18727/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 397381/1000000) (δ := 7813/1000000000) (ψ := -696637/1000000) 154 127
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t179 : ((-3508651443/2500000000000 : ℚ) : ℝ) ≤ stT154 179 := by
  have hc : ((-18777/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3508651443/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-18777/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c180 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-24019/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1223729/2000000) (δ := 7813/1000000000) (ψ := -696637/1000000) 154 127
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t180 : ((-71615481531/1250000000000 : ℚ) : ℝ) ≤ stT154 180 := by
  have hc : ((-384329/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71615481531/1250000000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-384329/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c181 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-987377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3728171/5000000) (δ := 7883/1000000000) (ψ := -696637/1000000) 154 128
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t181 : ((-146789910393/2000000000000 : ℚ) : ℝ) ≤ stT154 181 := by
  have hc : ((-987427/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-146789910393/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-987427/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c182 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-533947/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2667573/5000000) (δ := 7883/1000000000) (ψ := -696637/1000000) 154 128
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t182 : ((-316660221/8000000000 : ℚ) : ℝ) ≤ stT154 182 := by
  have hc : ((-533997/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316660221/8000000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-533997/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c183 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((138457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1612769/5000000) (δ := 193/25000000) (ψ := -696637/1000000) 154 128
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t183 : ((1598935023/78125000000 : ℚ) : ℝ) ≤ stT154 183 := by
  have hc : ((4326/15625 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1598935023/78125000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((4326/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c184 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((450011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -563721/5000000) (δ := 193/25000000) (ψ := -696637/1000000) 154 128
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t184 : ((165866864537/2500000000000 : ℚ) : ℝ) ≤ stT154 184 := by
  have hc : ((224993/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((165866864537/2500000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((224993/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c185 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((927279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 14989/156250) (δ := 7883/1000000000) (ψ := -696637/1000000) 154 128
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t185 : ((340855871003/5000000000000 : ℚ) : ℝ) ≤ stT154 185 := by
  have hc : ((927229/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((340855871003/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((927229/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c186 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((174683/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1517377/5000000) (δ := 7883/1000000000) (ψ := -696637/1000000) 154 128
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t186 : ((12806535863/500000000000 : ℚ) : ℝ) ≤ stT154 186 := by
  have hc : ((87329/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12806535863/500000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((87329/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c187 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-56483/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1274781/2500000) (δ := 7883/1000000000) (ψ := -696637/1000000) 154 128
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t187 : ((-165236253261/5000000000000 : ℚ) : ℝ) ≤ stT154 187 := by
  have hc : ((-225957/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-165236253261/5000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-225957/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c188 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-192177/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1430489/2000000) (δ := 193/25000000) (ψ := -696637/1000000) 154 128
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t188 : ((-5606671351/80000000000 : ℚ) : ℝ) ≤ stT154 188 := by
  have hc : ((-192187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5606671351/80000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-192187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c189 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-859569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1302611/2000000) (δ := 311/40000000) (ψ := -696637/1000000) 154 129
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t189 : ((-625280843267/10000000000000 : ℚ) : ℝ) ≤ stT154 189 := by
  have hc : ((-859619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-625280843267/10000000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-859619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c190 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-109977/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -448141/1000000) (δ := 311/40000000) (ψ := -696637/1000000) 154 129
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t190 : ((-39901960477/2500000000000 : ℚ) : ℝ) ≤ stT154 190 := by
  have hc : ((-55001/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).2
  have h0 : (0:ℝ) ≤ ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-39901960477/2500000000000 : ℚ) : ℝ)
      = ((725477/10000000 : ℚ) : ℝ) * ((-55001/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c191 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((276783/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2460391/10000000) (δ := 311/40000000) (ψ := -696637/1000000) 154 129
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t191 : ((50063723273/1250000000000 : ℚ) : ℝ) ≤ stT154 191 := by
  have hc : ((138379/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((50063723273/1250000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((138379/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c192 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((983847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449959/10000000) (δ := 1957/250000000) (ψ := -696637/1000000) 154 129
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t192 : ((709993505539/10000000000000 : ℚ) : ℝ) ≤ stT154 192 := by
  have hc : ((983797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((709993505539/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((983797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c193 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((813869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1550039/10000000) (δ := 1957/250000000) (ψ := -696637/1000000) 154 129
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t193 : ((117159824697/2000000000000 : ℚ) : ℝ) ≤ stT154 193 := by
  have hc : ((813819/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).1
  have hw2 : ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((143963/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117159824697/2000000000000 : ℚ) : ℝ)
      = ((143963/2000000 : ℚ) : ℝ) * ((813819/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c194 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((15429/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3539719/10000000) (δ := 1957/250000000) (ψ := -696637/1000000) 154 129
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t194 : ((86513939/7812500000 : ℚ) : ℝ) ≤ stT154 194 := by
  have hc : ((482/3125 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).1
  have hw2 : ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358979/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86513939/7812500000 : ℚ) : ℝ)
      = ((358979/5000000 : ℚ) : ℝ) * ((482/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c195 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-594679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2759579/5000000) (δ := 1957/250000000) (ψ := -696637/1000000) 154 129
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t195 : ((-85178871567/2000000000000 : ℚ) : ℝ) ≤ stT154 195 := by
  have hc : ((-594729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-85178871567/2000000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-594729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c196 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-989331/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7488471/10000000) (δ := 311/40000000) (ψ := -696637/1000000) 154 129
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t196 : ((-353350498483/5000000000000 : ℚ) : ℝ) ≤ stT154 196 := by
  have hc : ((-989381/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).2
  have h0 : (0:ℝ) ≤ ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-353350498483/5000000000000 : ℚ) : ℝ)
      = ((357143/5000000 : ℚ) : ℝ) * ((-989381/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c197 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-100447/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6260189/10000000) (δ := 1967/250000000) (ψ := -696637/1000000) 154 130
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t197 : ((-286280109923/5000000000000 : ℚ) : ℝ) ≤ stT154 197 := by
  have hc : ((-401813/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).2
  have h0 : (0:ℝ) ≤ ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-286280109923/5000000000000 : ℚ) : ℝ)
      = ((712471/10000000 : ℚ) : ℝ) * ((-401813/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c198 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-4779/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2155409/5000000) (δ := 1547/200000000) (ψ := -696637/1000000) 154 130
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t198 : ((-5435843763/500000000000 : ℚ) : ℝ) ≤ stT154 198 := by
  have hc : ((-76489/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5435843763/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-76489/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c199 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((291449/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -474253/2000000) (δ := 1547/200000000) (ψ := -696637/1000000) 154 130
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t199 : ((6455779267/156250000000 : ℚ) : ℝ) ≤ stT154 199 := by
  have hc : ((9107/15625 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6455779267/156250000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((9107/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c200 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((19689/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -441453/10000000) (δ := 1967/250000000) (ψ := -696637/1000000) 154 130
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t200 : ((870093933/12500000000 : ℚ) : ℝ) ≤ stT154 200 := by
  have hc : ((2461/2500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).1
  have hw2 : ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((353553/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((870093933/12500000000 : ℚ) : ℝ)
      = ((353553/5000000 : ℚ) : ℝ) * ((2461/2500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c201 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((8301/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1478773/10000000) (δ := 1967/250000000) (ψ := -696637/1000000) 154 130
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t201 : ((2341886469/40000000000 : ℚ) : ℝ) ≤ stT154 201 := by
  have hc : ((16601/20000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2341886469/40000000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((16601/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c202 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((106689/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3389413/10000000) (δ := 1547/200000000) (ψ := -696637/1000000) 154 130
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t202 : ((9381058801/625000000000 : ℚ) : ℝ) ≤ stT154 202 := by
  have hc : ((13333/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9381058801/625000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((13333/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c203 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-518817/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2645329/5000000) (δ := 1967/250000000) (ψ := -696637/1000000) 154 130
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t203 : ((-364173549221/10000000000000 : ℚ) : ℝ) ≤ stT154 203 := by
  have hc : ((-518867/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).2
  have h0 : (0:ℝ) ≤ ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364173549221/10000000000000 : ℚ) : ℝ)
      = ((701863/10000000 : ℚ) : ℝ) * ((-518867/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c204 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-19283/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1795637/2500000) (δ := 1967/250000000) (ψ := -696637/1000000) 154 130
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t204 : ((-3375379761/50000000000 : ℚ) : ℝ) ≤ stT154 204 := by
  have hc : ((-4821/5000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3375379761/50000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-4821/5000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c205 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-442457/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1328553/2000000) (δ := 7761/1000000000) (ψ := -696637/1000000) 154 131
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t205 : ((-154521572871/2500000000000 : ℚ) : ℝ) ≤ stT154 205 := by
  have hc : ((-221241/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154521572871/2500000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-221241/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c206 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-330577/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2384639/5000000) (δ := 7761/1000000000) (ψ := -696637/1000000) 154 131
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t206 : ((-115179536109/5000000000000 : ℚ) : ℝ) ≤ stT154 206 := by
  have hc : ((-330627/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).2
  have h0 : (0:ℝ) ≤ ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-115179536109/5000000000000 : ℚ) : ℝ)
      = ((348367/5000000 : ℚ) : ℝ) * ((-330627/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c207 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((7951/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2904877/10000000) (δ := 7761/1000000000) (ψ := -696637/1000000) 154 131
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t207 : ((13814079/500000000 : ℚ) : ℝ) ≤ stT154 207 := by
  have hc : ((159/400 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13814079/500000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((159/400 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c208 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((913179/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -524723/5000000) (δ := 3921/500000000) (ψ := -696637/1000000) 154 131
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t208 : ((5065126563/80000000000 : ℚ) : ℝ) ≤ stT154 208 := by
  have hc : ((913129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5065126563/80000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((913129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c209 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((949601/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 797091/10000000) (δ := 3921/500000000) (ψ := -696637/1000000) 154 131
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t209 : ((328408860207/5000000000000 : ℚ) : ℝ) ≤ stT154 209 := by
  have hc : ((949551/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).1
  have hw2 : ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((345857/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((328408860207/5000000000000 : ℚ) : ℝ)
      = ((345857/5000000 : ℚ) : ℝ) * ((949551/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c210 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((494163/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2634811/10000000) (δ := 7761/1000000000) (ψ := -696637/1000000) 154 131
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t210 : ((68194017469/2000000000000 : ℚ) : ℝ) ≤ stT154 210 := by
  have hc : ((494113/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((68194017469/2000000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((494113/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c211 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-106537/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 278987/625000) (δ := 7761/1000000000) (ψ := -696637/1000000) 154 131
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t211 : ((-36680185549/2500000000000 : ℚ) : ℝ) ≤ stT154 211 := by
  have hc : ((-53281/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36680185549/2500000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-53281/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c212 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-161847/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6284111/10000000) (δ := 3921/500000000) (ψ := -696637/1000000) 154 131
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t212 : ((-111163873171/2000000000000 : ℚ) : ℝ) ≤ stT154 212 := by
  have hc : ((-161857/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).2
  have h0 : (0:ℝ) ≤ ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-111163873171/2000000000000 : ℚ) : ℝ)
      = ((686803/10000000 : ℚ) : ℝ) * ((-161857/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c213 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-497661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7612081/10000000) (δ := 7749/1000000000) (ψ := -696637/1000000) 154 132
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t213 : ((-170504486327/2500000000000 : ℚ) : ℝ) ≤ stT154 213 := by
  have hc : ((-248843/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).2
  have h0 : (0:ℝ) ≤ ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-170504486327/2500000000000 : ℚ) : ℝ)
      = ((685189/10000000 : ℚ) : ℝ) * ((-248843/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c214 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-683623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -290439/500000) (δ := 3927/500000000) (ψ := -696637/1000000) 154 132
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t214 : ((-233674645689/5000000000000 : ℚ) : ℝ) ≤ stT154 214 := by
  have hc : ((-683673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-233674645689/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-683673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c215 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-34761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -401391/1000000) (δ := 3927/500000000) (ψ := -696637/1000000) 154 132
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t215 : ((-4748185589/2000000000000 : ℚ) : ℝ) ≤ stT154 215 := by
  have hc : ((-34811/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4748185589/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-34811/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c216 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((628679/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -556839/2500000) (δ := 3927/500000000) (ψ := -696637/1000000) 154 132
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t216 : ((427727343777/10000000000000 : ℚ) : ℝ) ≤ stT154 216 := by
  have hc : ((628629/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).1
  have hw2 : ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((680413/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((427727343777/10000000000000 : ℚ) : ℝ)
      = ((680413/10000000 : ℚ) : ℝ) * ((628629/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c217 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((98391/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -449079/10000000) (δ := 7749/1000000000) (ψ := -696637/1000000) 154 132
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t217 : ((8348593223/125000000000 : ℚ) : ℝ) ≤ stT154 217 := by
  have hc : ((49193/50000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).1
  have hw2 : ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((169711/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8348593223/125000000000 : ℚ) : ℝ)
      = ((169711/2500000 : ℚ) : ℝ) * ((49193/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c218 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((107951/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 264207/2000000) (δ := 3927/500000000) (ψ := -696637/1000000) 154 132
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t218 : ((58487488003/1000000000000 : ℚ) : ℝ) ≤ stT154 218 := by
  have hc : ((431779/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58487488003/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((431779/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c219 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((82799/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 616613/2000000) (δ := 7749/1000000000) (ψ := -696637/1000000) 154 132
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t219 : ((111883802301/5000000000000 : ℚ) : ℝ) ≤ stT154 219 := by
  have hc : ((165573/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111883802301/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((165573/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c220 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-89009/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 604631/1250000) (δ := 7749/1000000000) (ψ := -696637/1000000) 154 132
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t220 : ((-600182953/25000000000 : ℚ) : ℝ) ≤ stT154 220 := by
  have hc : ((-178043/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).2
  have h0 : (0:ℝ) ≤ ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-600182953/25000000000 : ℚ) : ℝ)
      = ((3371/50000 : ℚ) : ℝ) * ((-178043/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c221 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-218387/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 65831/100000) (δ := 7749/1000000000) (ψ := -696637/1000000) 154 132
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t221 : ((-293822893727/5000000000000 : ℚ) : ℝ) ≤ stT154 221 := by
  have hc : ((-436799/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-293822893727/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-436799/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c222 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-491293/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3693371/5000000) (δ := 491/62500000) (ψ := -696637/1000000) 154 133
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t222 : ((-164875757463/2500000000000 : ℚ) : ℝ) ≤ stT154 222 := by
  have hc : ((-245659/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164875757463/2500000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-245659/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c223 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-79737/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2828199/5000000) (δ := 491/62500000) (ψ := -696637/1000000) 154 133
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t223 : ((-4272005389/100000000000 : ℚ) : ℝ) ≤ stT154 223 := by
  have hc : ((-318973/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4272005389/100000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-318973/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c224 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-2721/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3933793/10000000) (δ := 7747/1000000000) (ψ := -696637/1000000) 154 133
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t224 : ((-925727367/5000000000000 : ℚ) : ℝ) ≤ stT154 224 := by
  have hc : ((-2771/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-925727367/5000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-2771/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c225 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((315661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2218849/10000000) (δ := 7747/1000000000) (ψ := -696637/1000000) 154 133
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t225 : ((26302973697/625000000000 : ℚ) : ℝ) ≤ stT154 225 := by
  have hc : ((78909/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26302973697/625000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((78909/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c226 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((979139/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -511547/10000000) (δ := 483/31250000) (ψ := -696637/1000000) 154 133
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t226 : ((65128021191/1000000000000 : ℚ) : ℝ) ≤ stT154 226 := by
  have hc : ((979089/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((65128021191/1000000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((979089/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c227 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((222289/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1188247/10000000) (δ := 7747/1000000000) (ψ := -696637/1000000) 154 133
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t227 : ((295060050819/5000000000000 : ℚ) : ℝ) ≤ stT154 227 := by
  have hc : ((444553/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295060050819/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((444553/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c228 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((406459/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2880553/10000000) (δ := 7747/1000000000) (ψ := -696637/1000000) 154 133
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t228 : ((134575431397/5000000000000 : ℚ) : ℝ) ≤ stT154 228 := by
  have hc : ((406409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((134575431397/5000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((406409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c229 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-252623/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4565467/10000000) (δ := 7747/1000000000) (ψ := -696637/1000000) 154 133
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t229 : ((-166971119187/10000000000000 : ℚ) : ℝ) ≤ stT154 229 := by
  have hc : ((-252673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-166971119187/10000000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-252673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c230 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-799471/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1560757/2500000) (δ := 491/62500000) (ψ := -696637/1000000) 154 133
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t230 : ((-527188956501/10000000000000 : ℚ) : ℝ) ≤ stT154 230 := by
  have hc : ((-799521/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-527188956501/10000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-799521/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c231 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-499859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1948663/2500000) (δ := 7839/1000000000) (ψ := -696637/1000000) 154 134
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t231 : ((-2569528731/39062500000 : ℚ) : ℝ) ≤ stT154 231 := by
  have hc : ((-124971/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2569528731/39062500000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-124971/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c232 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-385957/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3065803/5000000) (δ := 7839/1000000000) (ψ := -696637/1000000) 154 134
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t232 : ((-126704960203/2500000000000 : ℚ) : ℝ) ≤ stT154 232 := by
  have hc : ((-192991/250000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-126704960203/2500000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-192991/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c233 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-217719/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2237841/5000000) (δ := 1941/250000000) (ψ := -696637/1000000) 154 134
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t233 : ((-71332631409/5000000000000 : ℚ) : ℝ) ≤ stT154 233 := by
  have hc : ((-217769/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-71332631409/5000000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-217769/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c234 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((425993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2826843/10000000) (δ := 7839/1000000000) (ψ := -696637/1000000) 154 134
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t234 : ((6961186449/250000000000 : ℚ) : ℝ) ≤ stT154 234 := by
  have hc : ((425943/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6961186449/250000000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((425943/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c235 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((889741/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1185049/10000000) (δ := 7839/1000000000) (ψ := -696637/1000000) 154 134
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t235 : ((72546293831/1250000000000 : ℚ) : ℝ) ≤ stT154 235 := by
  have hc : ((889691/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((72546293831/1250000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((889691/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c236 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((49193/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 449777/10000000) (δ := 1941/250000000) (ψ := -696637/1000000) 154 134
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t236 : ((1000633151/15625000000 : ℚ) : ℝ) ≤ stT154 236 := by
  have hc : ((98381/100000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1000633151/15625000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((98381/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c237 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((674087/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 259709/1250000) (δ := 7839/1000000000) (ψ := -696637/1000000) 154 134
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t237 : ((437833540053/10000000000000 : ℚ) : ℝ) ≤ stT154 237 := by
  have hc : ((674037/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((437833540053/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((674037/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c238 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((91183/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 739743/2000000) (δ := 1941/250000000) (ψ := -696637/1000000) 154 134
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t238 : ((59072683999/10000000000000 : ℚ) : ℝ) ≤ stT154 238 := by
  have hc : ((91133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59072683999/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((91133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c239 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-52643/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5312981/10000000) (δ := 7839/1000000000) (ψ := -696637/1000000) 154 134
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t239 : ((-4256900107/125000000000 : ℚ) : ℝ) ≤ stT154 239 := by
  have hc : ((-6581/12500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-4256900107/125000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-6581/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c240 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-931097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 692051/1000000) (δ := 7839/1000000000) (ψ := -696637/1000000) 154 134
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t240 : ((-300526763103/5000000000000 : ℚ) : ℝ) ≤ stT154 240 := by
  have hc : ((-931147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-300526763103/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-931147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c241 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-482291/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7186623/10000000) (δ := 1933/250000000) (ψ := -696637/1000000) 154 135
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t241 : ((-77671806903/1250000000000 : ℚ) : ℝ) ≤ stT154 241 := by
  have hc : ((-120579/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-77671806903/1250000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-120579/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c242 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-617979/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1118483/2000000) (δ := 1933/250000000) (ψ := -696637/1000000) 154 135
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t242 : ((-15891379677/400000000000 : ℚ) : ℝ) ≤ stT154 242 := by
  have hc : ((-618029/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15891379677/400000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-618029/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c243 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-6223/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -400479/1000000) (δ := 7871/1000000000) (ψ := -696637/1000000) 154 135
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t243 : ((-3998475733/2000000000000 : ℚ) : ℝ) ≤ stT154 243 := by
  have hc : ((-6233/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3998475733/2000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-6233/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c244 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((282869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -302959/1250000) (δ := 7871/1000000000) (ψ := -696637/1000000) 154 135
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t244 : ((5658506353/156250000000 : ℚ) : ℝ) ≤ stT154 244 := by
  have hc : ((70711/125000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5658506353/156250000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((70711/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c245 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((471441/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -424521/5000000) (δ := 3883/250000000) (ψ := -696637/1000000) 154 135
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t245 : ((9411761513/156250000000 : ℚ) : ℝ) ≤ stT154 245 := by
  have hc : ((58927/62500 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9411761513/156250000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((58927/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c246 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((191781/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 359599/5000000) (δ := 1933/250000000) (ψ := -696637/1000000) 154 135
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t246 : ((15283573387/250000000000 : ℚ) : ℝ) ≤ stT154 246 := by
  have hc : ((191771/200000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15283573387/250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((191771/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c247 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((152957/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1140533/5000000) (δ := 1933/250000000) (ψ := -696637/1000000) 154 135
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t247 : ((48658069119/1250000000000 : ℚ) : ℝ) ≤ stT154 247 := by
  have hc : ((305889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).1
  have hw2 : ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((48658069119/1250000000000 : ℚ) : ℝ)
      = ((159071/2500000 : ℚ) : ℝ) * ((305889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c248 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((1807/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191831/500000) (δ := 1933/250000000) (ψ := -696637/1000000) 154 135
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t248 : ((458343/200000000 : ℚ) : ℝ) ≤ stT154 248 := by
  have hc : ((3609/100000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).1
  have hw2 : ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((127/2000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((458343/200000000 : ℚ) : ℝ)
      = ((127/2000 : ℚ) : ℝ) * ((3609/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c249 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-551001/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5385899/10000000) (δ := 7871/1000000000) (ψ := -696637/1000000) 154 135
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t249 : ((-13968591799/400000000000 : ℚ) : ℝ) ≤ stT154 249 := by
  have hc : ((-551051/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13968591799/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-551051/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_c250 :
    |Real.cos (((154 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((-233083/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6929017/10000000) (δ := 1933/250000000) (ψ := -696637/1000000) 154 135
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st154_t250 : ((-36855661887/625000000000 : ℚ) : ℝ) ≤ stT154 250 := by
  have hc : ((-466191/500000 : ℚ) : ℝ)
      ≤ Real.cos (((154 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st154_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36855661887/625000000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-466191/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st154_p1 : ((383477/500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT154 (i+1) := by
  rw [Finset.sum_range_one]
  exact st154_t1

theorem st154_p2 : ((6697328840409/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT154 (i+1))
      = (∑ i ∈ Finset.range 1, stT154 (i+1)) + stT154 2 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 1
    simpa using h
  have hprev := st154_p1
  have hstep := st154_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p3 : ((4751647056837/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT154 (i+1))
      = (∑ i ∈ Finset.range 2, stT154 (i+1)) + stT154 3 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 2
    simpa using h
  have hprev := st154_p2
  have hstep := st154_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p4 : ((5812199556837/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT154 (i+1))
      = (∑ i ∈ Finset.range 3, stT154 (i+1)) + stT154 4 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 3
    simpa using h
  have hprev := st154_p3
  have hstep := st154_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p5 : ((4767467219979/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT154 (i+1))
      = (∑ i ∈ Finset.range 4, stT154 (i+1)) + stT154 5 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 4
    simpa using h
  have hprev := st154_p4
  have hstep := st154_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p6 : ((11547526622523/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT154 (i+1))
      = (∑ i ∈ Finset.range 5, stT154 (i+1)) + stT154 6 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 5
    simpa using h
  have hprev := st154_p5
  have hstep := st154_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p7 : ((97488265779/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT154 (i+1))
      = (∑ i ∈ Finset.range 6, stT154 (i+1)) + stT154 7 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 6
    simpa using h
  have hprev := st154_p6
  have hstep := st154_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p8 : ((5498883876141/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT154 (i+1))
      = (∑ i ∈ Finset.range 7, stT154 (i+1)) + stT154 8 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 7
    simpa using h
  have hprev := st154_p7
  have hstep := st154_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p9 : ((192157514931/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT154 (i+1))
      = (∑ i ∈ Finset.range 8, stT154 (i+1)) + stT154 9 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 8
    simpa using h
  have hprev := st154_p8
  have hstep := st154_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p10 : ((13859576081461/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT154 (i+1))
      = (∑ i ∈ Finset.range 9, stT154 (i+1)) + stT154 10 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 9
    simpa using h
  have hprev := st154_p9
  have hstep := st154_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p11 : ((1872177522609/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT154 (i+1))
      = (∑ i ∈ Finset.range 10, stT154 (i+1)) + stT154 11 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 10
    simpa using h
  have hprev := st154_p10
  have hstep := st154_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p12 : ((328276079399/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT154 (i+1))
      = (∑ i ∈ Finset.range 11, stT154 (i+1)) + stT154 12 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 11
    simpa using h
  have hprev := st154_p11
  have hstep := st154_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p13 : ((355731177779/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT154 (i+1))
      = (∑ i ∈ Finset.range 12, stT154 (i+1)) + stT154 13 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 12
    simpa using h
  have hprev := st154_p12
  have hstep := st154_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p14 : ((567176414247/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT154 (i+1))
      = (∑ i ∈ Finset.range 13, stT154 (i+1)) + stT154 14 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 13
    simpa using h
  have hprev := st154_p13
  have hstep := st154_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p15 : ((16864462813143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT154 (i+1))
      = (∑ i ∈ Finset.range 14, stT154 (i+1)) + stT154 15 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 14
    simpa using h
  have hprev := st154_p14
  have hstep := st154_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p16 : ((18006421563143/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT154 (i+1))
      = (∑ i ∈ Finset.range 15, stT154 (i+1)) + stT154 16 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 15
    simpa using h
  have hprev := st154_p15
  have hstep := st154_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p17 : ((33718322009651/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT154 (i+1))
      = (∑ i ∈ Finset.range 16, stT154 (i+1)) + stT154 17 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 16
    simpa using h
  have hprev := st154_p16
  have hstep := st154_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p18 : ((1439010782783/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT154 (i+1))
      = (∑ i ∈ Finset.range 17, stT154 (i+1)) + stT154 18 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 17
    simpa using h
  have hprev := st154_p17
  have hstep := st154_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p19 : ((1422568552397/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT154 (i+1))
      = (∑ i ∈ Finset.range 18, stT154 (i+1)) + stT154 19 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 18
    simpa using h
  have hprev := st154_p18
  have hstep := st154_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p20 : ((33384537208817/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT154 (i+1))
      = (∑ i ∈ Finset.range 19, stT154 (i+1)) + stT154 20 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 19
    simpa using h
  have hprev := st154_p19
  have hstep := st154_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p21 : ((33134014330901/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT154 (i+1))
      = (∑ i ∈ Finset.range 20, stT154 (i+1)) + stT154 21 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 20
    simpa using h
  have hprev := st154_p20
  have hstep := st154_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p22 : ((3461176594679/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT154 (i+1))
      = (∑ i ∈ Finset.range 21, stT154 (i+1)) + stT154 22 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 21
    simpa using h
  have hprev := st154_p21
  have hstep := st154_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p23 : ((18317894060359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT154 (i+1))
      = (∑ i ∈ Finset.range 22, stT154 (i+1)) + stT154 23 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 22
    simpa using h
  have hprev := st154_p22
  have hstep := st154_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p24 : ((38676100356063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT154 (i+1))
      = (∑ i ∈ Finset.range 23, stT154 (i+1)) + stT154 24 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 23
    simpa using h
  have hprev := st154_p23
  have hstep := st154_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p25 : ((40674984356063/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT154 (i+1))
      = (∑ i ∈ Finset.range 24, stT154 (i+1)) + stT154 25 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 24
    simpa using h
  have hprev := st154_p24
  have hstep := st154_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p26 : ((2662026329473/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT154 (i+1))
      = (∑ i ∈ Finset.range 25, stT154 (i+1)) + stT154 26 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 25
    simpa using h
  have hprev := st154_p25
  have hstep := st154_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p27 : ((5510717130821/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT154 (i+1))
      = (∑ i ∈ Finset.range 26, stT154 (i+1)) + stT154 27 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 26
    simpa using h
  have hprev := st154_p26
  have hstep := st154_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p28 : ((5558964286481/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT154 (i+1))
      = (∑ i ∈ Finset.range 27, stT154 (i+1)) + stT154 28 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 27
    simpa using h
  have hprev := st154_p27
  have hstep := st154_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p29 : ((10828389519851/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT154 (i+1))
      = (∑ i ∈ Finset.range 28, stT154 (i+1)) + stT154 29 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 28
    simpa using h
  have hprev := st154_p28
  have hstep := st154_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p30 : ((5189062970341/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT154 (i+1))
      = (∑ i ∈ Finset.range 29, stT154 (i+1)) + stT154 30 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 29
    simpa using h
  have hprev := st154_p29
  have hstep := st154_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p31 : ((10301115635297/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT154 (i+1))
      = (∑ i ∈ Finset.range 30, stT154 (i+1)) + stT154 31 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 30
    simpa using h
  have hprev := st154_p30
  have hstep := st154_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p32 : ((21432718014681/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT154 (i+1))
      = (∑ i ∈ Finset.range 31, stT154 (i+1)) + stT154 32 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 31
    simpa using h
  have hprev := st154_p31
  have hstep := st154_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p33 : ((21752007667049/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT154 (i+1))
      = (∑ i ∈ Finset.range 32, stT154 (i+1)) + stT154 33 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 32
    simpa using h
  have hprev := st154_p32
  have hstep := st154_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p34 : ((81732155873/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT154 (i+1))
      = (∑ i ∈ Finset.range 33, stT154 (i+1)) + stT154 34 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 33
    simpa using h
  have hprev := st154_p33
  have hstep := st154_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p35 : ((2614122379079/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT154 (i+1))
      = (∑ i ∈ Finset.range 34, stT154 (i+1)) + stT154 35 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 34
    simpa using h
  have hprev := st154_p34
  have hstep := st154_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p36 : ((5423083846889/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT154 (i+1))
      = (∑ i ∈ Finset.range 35, stT154 (i+1)) + stT154 36 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 35
    simpa using h
  have hprev := st154_p35
  have hstep := st154_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p37 : ((21072205097661/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT154 (i+1))
      = (∑ i ∈ Finset.range 36, stT154 (i+1)) + stT154 37 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 36
    simpa using h
  have hprev := st154_p36
  have hstep := st154_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p38 : ((20982626385361/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT154 (i+1))
      = (∑ i ∈ Finset.range 37, stT154 (i+1)) + stT154 38 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 37
    simpa using h
  have hprev := st154_p37
  have hstep := st154_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p39 : ((43285366441213/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT154 (i+1))
      = (∑ i ∈ Finset.range 38, stT154 (i+1)) + stT154 39 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 38
    simpa using h
  have hprev := st154_p38
  have hstep := st154_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p40 : ((4172330072097/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT154 (i+1))
      = (∑ i ∈ Finset.range 39, stT154 (i+1)) + stT154 40 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 39
    simpa using h
  have hprev := st154_p39
  have hstep := st154_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p41 : ((42792242542779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT154 (i+1))
      = (∑ i ∈ Finset.range 40, stT154 (i+1)) + stT154 41 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 40
    simpa using h
  have hprev := st154_p40
  have hstep := st154_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p42 : ((42509105061983/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT154 (i+1))
      = (∑ i ∈ Finset.range 41, stT154 (i+1)) + stT154 42 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 41
    simpa using h
  have hprev := st154_p41
  have hstep := st154_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p43 : ((42061838868071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT154 (i+1))
      = (∑ i ∈ Finset.range 42, stT154 (i+1)) + stT154 43 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 42
    simpa using h
  have hprev := st154_p42
  have hstep := st154_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p44 : ((43028807899811/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT154 (i+1))
      = (∑ i ∈ Finset.range 43, stT154 (i+1)) + stT154 44 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 43
    simpa using h
  have hprev := st154_p43
  have hstep := st154_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p45 : ((41761911399491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT154 (i+1))
      = (∑ i ∈ Finset.range 44, stT154 (i+1)) + stT154 45 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 44
    simpa using h
  have hprev := st154_p44
  have hstep := st154_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p46 : ((10791266826491/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT154 (i+1))
      = (∑ i ∈ Finset.range 45, stT154 (i+1)) + stT154 46 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 45
    simpa using h
  have hprev := st154_p45
  have hstep := st154_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p47 : ((10430237823641/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT154 (i+1))
      = (∑ i ∈ Finset.range 46, stT154 (i+1)) + stT154 47 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 46
    simpa using h
  have hprev := st154_p46
  have hstep := st154_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p48 : ((43163040247439/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT154 (i+1))
      = (∑ i ∈ Finset.range 47, stT154 (i+1)) + stT154 48 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 47
    simpa using h
  have hprev := st154_p47
  have hstep := st154_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p49 : ((41734433961711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT154 (i+1))
      = (∑ i ∈ Finset.range 48, stT154 (i+1)) + stT154 49 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 48
    simpa using h
  have hprev := st154_p48
  have hstep := st154_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p50 : ((4314757640247/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT154 (i+1))
      = (∑ i ∈ Finset.range 49, stT154 (i+1)) + stT154 50 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 49
    simpa using h
  have hprev := st154_p49
  have hstep := st154_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p51 : ((20879484072443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT154 (i+1))
      = (∑ i ∈ Finset.range 50, stT154 (i+1)) + stT154 51 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 50
    simpa using h
  have hprev := st154_p50
  have hstep := st154_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p52 : ((21545667678443/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT154 (i+1))
      = (∑ i ∈ Finset.range 51, stT154 (i+1)) + stT154 52 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 51
    simpa using h
  have hprev := st154_p51
  have hstep := st154_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p53 : ((10469655987121/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT154 (i+1))
      = (∑ i ∈ Finset.range 52, stT154 (i+1)) + stT154 53 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 52
    simpa using h
  have hprev := st154_p52
  have hstep := st154_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p54 : ((2143620978833/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT154 (i+1))
      = (∑ i ∈ Finset.range 53, stT154 (i+1)) + stT154 54 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 53
    simpa using h
  have hprev := st154_p53
  have hstep := st154_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p55 : ((2111118201353/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT154 (i+1))
      = (∑ i ∈ Finset.range 54, stT154 (i+1)) + stT154 55 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 54
    simpa using h
  have hprev := st154_p54
  have hstep := st154_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p56 : ((21201897814493/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT154 (i+1))
      = (∑ i ∈ Finset.range 55, stT154 (i+1)) + stT154 56 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 55
    simpa using h
  have hprev := st154_p55
  have hstep := st154_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p57 : ((21384638858671/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT154 (i+1))
      = (∑ i ∈ Finset.range 56, stT154 (i+1)) + stT154 57 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 56
    simpa using h
  have hprev := st154_p56
  have hstep := st154_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p58 : ((41881050958897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT154 (i+1))
      = (∑ i ∈ Finset.range 57, stT154 (i+1)) + stT154 58 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 57
    simpa using h
  have hprev := st154_p57
  have hstep := st154_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p59 : ((10779311334517/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT154 (i+1))
      = (∑ i ∈ Finset.range 58, stT154 (i+1)) + stT154 59 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 58
    simpa using h
  have hprev := st154_p58
  have hstep := st154_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p60 : ((20930748541779/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT154 (i+1))
      = (∑ i ∈ Finset.range 59, stT154 (i+1)) + stT154 60 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 59
    simpa using h
  have hprev := st154_p59
  have hstep := st154_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p61 : ((21362521920947/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT154 (i+1))
      = (∑ i ∈ Finset.range 60, stT154 (i+1)) + stT154 61 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 60
    simpa using h
  have hprev := st154_p60
  have hstep := st154_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p62 : ((1331082382079/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT154 (i+1))
      = (∑ i ∈ Finset.range 61, stT154 (i+1)) + stT154 62 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 61
    simpa using h
  have hprev := st154_p61
  have hstep := st154_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p63 : ((20954852578437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT154 (i+1))
      = (∑ i ∈ Finset.range 62, stT154 (i+1)) + stT154 63 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 62
    simpa using h
  have hprev := st154_p62
  have hstep := st154_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p64 : ((21555528203437/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT154 (i+1))
      = (∑ i ∈ Finset.range 63, stT154 (i+1)) + stT154 64 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 63
    simpa using h
  have hprev := st154_p63
  have hstep := st154_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p65 : ((21003760015811/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT154 (i+1))
      = (∑ i ∈ Finset.range 64, stT154 (i+1)) + stT154 65 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 64
    simpa using h
  have hprev := st154_p64
  have hstep := st154_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p66 : ((2118923844553/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT154 (i+1))
      = (∑ i ∈ Finset.range 65, stT154 (i+1)) + stT154 66 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 65
    simpa using h
  have hprev := st154_p65
  have hstep := st154_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p67 : ((10746250995269/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT154 (i+1))
      = (∑ i ∈ Finset.range 66, stT154 (i+1)) + stT154 67 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 66
    simpa using h
  have hprev := st154_p66
  have hstep := st154_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p68 : ((81629593911/19531250000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT154 (i+1))
      = (∑ i ∈ Finset.range 67, stT154 (i+1)) + stT154 68 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 67
    simpa using h
  have hprev := st154_p67
  have hstep := st154_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p69 : ((1067833107747/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT154 (i+1))
      = (∑ i ∈ Finset.range 68, stT154 (i+1)) + stT154 69 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 68
    simpa using h
  have hprev := st154_p68
  have hstep := st154_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p70 : ((2673846894661/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT154 (i+1))
      = (∑ i ∈ Finset.range 69, stT154 (i+1)) + stT154 70 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 69
    simpa using h
  have hprev := st154_p69
  have hstep := st154_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p71 : ((20886882354863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT154 (i+1))
      = (∑ i ∈ Finset.range 70, stT154 (i+1)) + stT154 71 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 70
    simpa using h
  have hprev := st154_p70
  have hstep := st154_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p72 : ((42844325280637/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT154 (i+1))
      = (∑ i ∈ Finset.range 71, stT154 (i+1)) + stT154 72 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 71
    simpa using h
  have hprev := st154_p71
  have hstep := st154_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p73 : ((42701669614017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT154 (i+1))
      = (∑ i ∈ Finset.range 72, stT154 (i+1)) + stT154 73 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 72
    simpa using h
  have hprev := st154_p72
  have hstep := st154_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p74 : ((41773799072249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT154 (i+1))
      = (∑ i ∈ Finset.range 73, stT154 (i+1)) + stT154 74 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 73
    simpa using h
  have hprev := st154_p73
  have hstep := st154_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p75 : ((42824365916849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT154 (i+1))
      = (∑ i ∈ Finset.range 74, stT154 (i+1)) + stT154 75 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 74
    simpa using h
  have hprev := st154_p74
  have hstep := st154_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p76 : ((42777138380261/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT154 (i+1))
      = (∑ i ∈ Finset.range 75, stT154 (i+1)) + stT154 76 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 75
    simpa using h
  have hprev := st154_p75
  have hstep := st154_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p77 : ((8353614621591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT154 (i+1))
      = (∑ i ∈ Finset.range 76, stT154 (i+1)) + stT154 77 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 76
    simpa using h
  have hprev := st154_p76
  have hstep := st154_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p78 : ((10663699147949/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT154 (i+1))
      = (∑ i ∈ Finset.range 77, stT154 (i+1)) + stT154 78 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 77
    simpa using h
  have hprev := st154_p77
  have hstep := st154_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p79 : ((42965684006897/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT154 (i+1))
      = (∑ i ∈ Finset.range 78, stT154 (i+1)) + stT154 79 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 78
    simpa using h
  have hprev := st154_p78
  have hstep := st154_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p80 : ((41851756545779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT154 (i+1))
      = (∑ i ∈ Finset.range 79, stT154 (i+1)) + stT154 80 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 79
    simpa using h
  have hprev := st154_p79
  have hstep := st154_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p81 : ((42313465388497/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT154 (i+1))
      = (∑ i ∈ Finset.range 80, stT154 (i+1)) + stT154 81 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 80
    simpa using h
  have hprev := st154_p80
  have hstep := st154_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p82 : ((10780847195713/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT154 (i+1))
      = (∑ i ∈ Finset.range 81, stT154 (i+1)) + stT154 82 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 81
    simpa using h
  have hprev := st154_p81
  have hstep := st154_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p83 : ((843498001991/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT154 (i+1))
      = (∑ i ∈ Finset.range 82, stT154 (i+1)) + stT154 83 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 82
    simpa using h
  have hprev := st154_p82
  have hstep := st154_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p84 : ((4190070263601/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT154 (i+1))
      = (∑ i ∈ Finset.range 83, stT154 (i+1)) + stT154 84 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 83
    simpa using h
  have hprev := st154_p83
  have hstep := st154_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p85 : ((21492648574727/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT154 (i+1))
      = (∑ i ∈ Finset.range 84, stT154 (i+1)) + stT154 85 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 84
    simpa using h
  have hprev := st154_p84
  have hstep := st154_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p86 : ((21370691834583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT154 (i+1))
      = (∑ i ∈ Finset.range 85, stT154 (i+1)) + stT154 86 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 85
    simpa using h
  have hprev := st154_p85
  have hstep := st154_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p87 : ((10442571825063/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT154 (i+1))
      = (∑ i ∈ Finset.range 86, stT154 (i+1)) + stT154 87 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 86
    simpa using h
  have hprev := st154_p86
  have hstep := st154_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p88 : ((42395612122073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT154 (i+1))
      = (∑ i ∈ Finset.range 87, stT154 (i+1)) + stT154 88 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 87
    simpa using h
  have hprev := st154_p87
  have hstep := st154_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p89 : ((862738229681/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT154 (i+1))
      = (∑ i ∈ Finset.range 88, stT154 (i+1)) + stT154 89 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 88
    simpa using h
  have hprev := st154_p88
  have hstep := st154_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p90 : ((21140907188481/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT154 (i+1))
      = (∑ i ∈ Finset.range 89, stT154 (i+1)) + stT154 90 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 89
    simpa using h
  have hprev := st154_p89
  have hstep := st154_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p91 : ((41784926238677/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT154 (i+1))
      = (∑ i ∈ Finset.range 90, stT154 (i+1)) + stT154 91 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 90
    simpa using h
  have hprev := st154_p90
  have hstep := st154_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p92 : ((1710099782657/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT154 (i+1))
      = (∑ i ∈ Finset.range 91, stT154 (i+1)) + stT154 92 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 91
    simpa using h
  have hprev := st154_p91
  have hstep := st154_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p93 : ((43046389292747/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT154 (i+1))
      = (∑ i ∈ Finset.range 92, stT154 (i+1)) + stT154 93 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 92
    simpa using h
  have hprev := st154_p92
  have hstep := st154_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p94 : ((42037819478579/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT154 (i+1))
      = (∑ i ∈ Finset.range 93, stT154 (i+1)) + stT154 94 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 93
    simpa using h
  have hprev := st154_p93
  have hstep := st154_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p95 : ((41882129217287/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT154 (i+1))
      = (∑ i ∈ Finset.range 94, stT154 (i+1)) + stT154 95 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 94
    simpa using h
  have hprev := st154_p94
  have hstep := st154_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p96 : ((42896473424907/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT154 (i+1))
      = (∑ i ∈ Finset.range 95, stT154 (i+1)) + stT154 96 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 95
    simpa using h
  have hprev := st154_p95
  have hstep := st154_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p97 : ((42983056039711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT154 (i+1))
      = (∑ i ∈ Finset.range 96, stT154 (i+1)) + stT154 97 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 96
    simpa using h
  have hprev := st154_p96
  have hstep := st154_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p98 : ((41975824402187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT154 (i+1))
      = (∑ i ∈ Finset.range 97, stT154 (i+1)) + stT154 98 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 97
    simpa using h
  have hprev := st154_p97
  have hstep := st154_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p99 : ((41891400205149/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT154 (i+1))
      = (∑ i ∈ Finset.range 98, stT154 (i+1)) + stT154 99 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 98
    simpa using h
  have hprev := st154_p98
  have hstep := st154_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p100 : ((42885619210929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT154 (i+1))
      = (∑ i ∈ Finset.range 99, stT154 (i+1)) + stT154 100 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 99
    simpa using h
  have hprev := st154_p99
  have hstep := st154_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p101 : ((2689366919991/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT154 (i+1))
      = (∑ i ∈ Finset.range 100, stT154 (i+1)) + stT154 101 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 100
    simpa using h
  have hprev := st154_p100
  have hstep := st154_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p102 : ((657175447429/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT154 (i+1))
      = (∑ i ∈ Finset.range 101, stT154 (i+1)) + stT154 102 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 101
    simpa using h
  have hprev := st154_p101
  have hstep := st154_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p103 : ((20899399509573/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT154 (i+1))
      = (∑ i ∈ Finset.range 102, stT154 (i+1)) + stT154 103 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 102
    simpa using h
  have hprev := st154_p102
  have hstep := st154_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p104 : ((21359890173663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT154 (i+1))
      = (∑ i ∈ Finset.range 103, stT154 (i+1)) + stT154 104 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 103
    simpa using h
  have hprev := st154_p103
  have hstep := st154_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p105 : ((21570959777463/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT154 (i+1))
      = (∑ i ∈ Finset.range 104, stT154 (i+1)) + stT154 105 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 104
    simpa using h
  have hprev := st154_p104
  have hstep := st154_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p106 : ((21159077207589/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT154 (i+1))
      = (∑ i ∈ Finset.range 105, stT154 (i+1)) + stT154 106 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 105
    simpa using h
  have hprev := st154_p105
  have hstep := st154_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p107 : ((521347514291/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT154 (i+1))
      = (∑ i ∈ Finset.range 106, stT154 (i+1)) + stT154 107 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 106
    simpa using h
  have hprev := st154_p106
  have hstep := st154_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p108 : ((2118159577139/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT154 (i+1))
      = (∑ i ∈ Finset.range 107, stT154 (i+1)) + stT154 108 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 107
    simpa using h
  have hprev := st154_p107
  have hstep := st154_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p109 : ((10788701978163/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT154 (i+1))
      = (∑ i ∈ Finset.range 108, stT154 (i+1)) + stT154 109 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 108
    simpa using h
  have hprev := st154_p108
  have hstep := st154_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p110 : ((42754255245963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT154 (i+1))
      = (∑ i ∈ Finset.range 109, stT154 (i+1)) + stT154 110 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 109
    simpa using h
  have hprev := st154_p109
  have hstep := st154_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p111 : ((1673443072557/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT154 (i+1))
      = (∑ i ∈ Finset.range 110, stT154 (i+1)) + stT154 111 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 110
    simpa using h
  have hprev := st154_p110
  have hstep := st154_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p112 : ((2618691595381/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT154 (i+1))
      = (∑ i ∈ Finset.range 111, stT154 (i+1)) + stT154 112 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 111
    simpa using h
  have hprev := st154_p111
  have hstep := st154_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p113 : ((2676947680411/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT154 (i+1))
      = (∑ i ∈ Finset.range 112, stT154 (i+1)) + stT154 113 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 112
    simpa using h
  have hprev := st154_p112
  have hstep := st154_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p114 : ((10787867802559/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT154 (i+1))
      = (∑ i ∈ Finset.range 113, stT154 (i+1)) + stT154 114 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 113
    simpa using h
  have hprev := st154_p113
  have hstep := st154_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p115 : ((42368822561251/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT154 (i+1))
      = (∑ i ∈ Finset.range 114, stT154 (i+1)) + stT154 115 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 114
    simpa using h
  have hprev := st154_p114
  have hstep := st154_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p116 : ((20847390377973/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT154 (i+1))
      = (∑ i ∈ Finset.range 115, stT154 (i+1)) + stT154 116 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 115
    simpa using h
  have hprev := st154_p115
  have hstep := st154_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p117 : ((21072841721473/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT154 (i+1))
      = (∑ i ∈ Finset.range 116, stT154 (i+1)) + stT154 117 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 116
    simpa using h
  have hprev := st154_p116
  have hstep := st154_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p118 : ((5379716452051/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT154 (i+1))
      = (∑ i ∈ Finset.range 117, stT154 (i+1)) + stT154 118 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 117
    simpa using h
  have hprev := st154_p117
  have hstep := st154_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p119 : ((21528847274377/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT154 (i+1))
      = (∑ i ∈ Finset.range 118, stT154 (i+1)) + stT154 119 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 118
    simpa using h
  have hprev := st154_p118
  have hstep := st154_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p120 : ((42186610218779/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT154 (i+1))
      = (∑ i ∈ Finset.range 119, stT154 (i+1)) + stT154 120 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 119
    simpa using h
  have hprev := st154_p119
  have hstep := st154_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p121 : ((41675741076783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT154 (i+1))
      = (∑ i ∈ Finset.range 120, stT154 (i+1)) + stT154 121 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 120
    simpa using h
  have hprev := st154_p120
  have hstep := st154_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p122 : ((42238483827273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT154 (i+1))
      = (∑ i ∈ Finset.range 121, stT154 (i+1)) + stT154 122 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 121
    simpa using h
  have hprev := st154_p121
  have hstep := st154_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p123 : ((269270038239/62500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT154 (i+1))
      = (∑ i ∈ Finset.range 122, stT154 (i+1)) + stT154 123 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 122
    simpa using h
  have hprev := st154_p122
  have hstep := st154_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p124 : ((43053232671061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT154 (i+1))
      = (∑ i ∈ Finset.range 123, stT154 (i+1)) + stT154 124 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 123
    simpa using h
  have hprev := st154_p123
  have hstep := st154_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p125 : ((337590735613/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT154 (i+1))
      = (∑ i ∈ Finset.range 124, stT154 (i+1)) + stT154 125 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 124
    simpa using h
  have hprev := st154_p124
  have hstep := st154_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p126 : ((1301993081029/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT154 (i+1))
      = (∑ i ∈ Finset.range 125, stT154 (i+1)) + stT154 126 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 125
    simpa using h
  have hprev := st154_p125
  have hstep := st154_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p127 : ((10536239729889/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT154 (i+1))
      = (∑ i ∈ Finset.range 126, stT154 (i+1)) + stT154 127 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 126
    simpa using h
  have hprev := st154_p126
  have hstep := st154_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p128 : ((21504667310873/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT154 (i+1))
      = (∑ i ∈ Finset.range 127, stT154 (i+1)) + stT154 128 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 127
    simpa using h
  have hprev := st154_p127
  have hstep := st154_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p129 : ((1348480688203/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT154 (i+1))
      = (∑ i ∈ Finset.range 128, stT154 (i+1)) + stT154 129 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 128
    simpa using h
  have hprev := st154_p128
  have hstep := st154_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p130 : ((21200375538673/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT154 (i+1))
      = (∑ i ∈ Finset.range 129, stT154 (i+1)) + stT154 130 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 129
    simpa using h
  have hprev := st154_p129
  have hstep := st154_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p131 : ((20849015072923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT154 (i+1))
      = (∑ i ∈ Finset.range 130, stT154 (i+1)) + stT154 131 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 130
    simpa using h
  have hprev := st154_p130
  have hstep := st154_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p132 : ((4190208651973/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT154 (i+1))
      = (∑ i ∈ Finset.range 131, stT154 (i+1)) + stT154 132 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 131
    simpa using h
  have hprev := st154_p131
  have hstep := st154_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p133 : ((42756382250037/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT154 (i+1))
      = (∑ i ∈ Finset.range 132, stT154 (i+1)) + stT154 133 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 132
    simpa using h
  have hprev := st154_p132
  have hstep := st154_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p134 : ((8647258404657/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT154 (i+1))
      = (∑ i ∈ Finset.range 133, stT154 (i+1)) + stT154 134 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 133
    simpa using h
  have hprev := st154_p133
  have hstep := st154_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p135 : ((5347757381389/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT154 (i+1))
      = (∑ i ∈ Finset.range 134, stT154 (i+1)) + stT154 135 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 134
    simpa using h
  have hprev := st154_p134
  have hstep := st154_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p136 : ((1677234436289/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT154 (i+1))
      = (∑ i ∈ Finset.range 135, stT154 (i+1)) + stT154 136 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 135
    simpa using h
  have hprev := st154_p135
  have hstep := st154_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p137 : ((41661317793089/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT154 (i+1))
      = (∑ i ∈ Finset.range 136, stT154 (i+1)) + stT154 137 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 136
    simpa using h
  have hprev := st154_p136
  have hstep := st154_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p138 : ((42271378918049/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT154 (i+1))
      = (∑ i ∈ Finset.range 137, stT154 (i+1)) + stT154 138 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 137
    simpa using h
  have hprev := st154_p137
  have hstep := st154_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p139 : ((8614182461961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT154 (i+1))
      = (∑ i ∈ Finset.range 138, stT154 (i+1)) + stT154 139 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 138
    simpa using h
  have hprev := st154_p138
  have hstep := st154_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p140 : ((43177618073229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT154 (i+1))
      = (∑ i ∈ Finset.range 139, stT154 (i+1)) + stT154 140 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 139
    simpa using h
  have hprev := st154_p139
  have hstep := st154_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p141 : ((42483166059597/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT154 (i+1))
      = (∑ i ∈ Finset.range 140, stT154 (i+1)) + stT154 141 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 140
    simpa using h
  have hprev := st154_p140
  have hstep := st154_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p142 : ((1669660014589/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT154 (i+1))
      = (∑ i ∈ Finset.range 141, stT154 (i+1)) + stT154 142 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 141
    simpa using h
  have hprev := st154_p141
  have hstep := st154_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p143 : ((41738867871761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT154 (i+1))
      = (∑ i ∈ Finset.range 142, stT154 (i+1)) + stT154 143 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 142
    simpa using h
  have hprev := st154_p142
  have hstep := st154_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p144 : ((42469852579367/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT154 (i+1))
      = (∑ i ∈ Finset.range 143, stT154 (i+1)) + stT154 144 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 143
    simpa using h
  have hprev := st154_p143
  have hstep := st154_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p145 : ((43171190913263/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT154 (i+1))
      = (∑ i ∈ Finset.range 144, stT154 (i+1)) + stT154 145 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 144
    simpa using h
  have hprev := st154_p144
  have hstep := st154_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p146 : ((8625518029273/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT154 (i+1))
      = (∑ i ∈ Finset.range 145, stT154 (i+1)) + stT154 146 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 145
    simpa using h
  have hprev := st154_p145
  have hstep := st154_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p147 : ((423910594793/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT154 (i+1))
      = (∑ i ∈ Finset.range 146, stT154 (i+1)) + stT154 147 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 146
    simpa using h
  have hprev := st154_p146
  have hstep := st154_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p148 : ((4170215697773/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT154 (i+1))
      = (∑ i ∈ Finset.range 147, stT154 (i+1)) + stT154 148 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 147
    simpa using h
  have hprev := st154_p147
  have hstep := st154_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p149 : ((8347528393699/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT154 (i+1))
      = (∑ i ∈ Finset.range 148, stT154 (i+1)) + stT154 149 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 148
    simpa using h
  have hprev := st154_p148
  have hstep := st154_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p150 : ((42455187634751/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT154 (i+1))
      = (∑ i ∈ Finset.range 149, stT154 (i+1)) + stT154 150 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 149
    simpa using h
  have hprev := st154_p149
  have hstep := st154_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p151 : ((43158953124727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT154 (i+1))
      = (∑ i ∈ Finset.range 150, stT154 (i+1)) + stT154 151 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 150
    simpa using h
  have hprev := st154_p150
  have hstep := st154_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p152 : ((8636380517237/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT154 (i+1))
      = (∑ i ∈ Finset.range 151, stT154 (i+1)) + stT154 152 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 151
    simpa using h
  have hprev := st154_p151
  have hstep := st154_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p153 : ((42509772547951/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT154 (i+1))
      = (∑ i ∈ Finset.range 152, stT154 (i+1)) + stT154 153 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 152
    simpa using h
  have hprev := st154_p152
  have hstep := st154_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p154 : ((2610748318531/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT154 (i+1))
      = (∑ i ∈ Finset.range 153, stT154 (i+1)) + stT154 154 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 153
    simpa using h
  have hprev := st154_p153
  have hstep := st154_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p155 : ((10410977125729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT154 (i+1))
      = (∑ i ∈ Finset.range 154, stT154 (i+1)) + stT154 155 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 154
    simpa using h
  have hprev := st154_p154
  have hstep := st154_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p156 : ((10558710217729/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT154 (i+1))
      = (∑ i ∈ Finset.range 155, stT154 (i+1)) + stT154 156 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 155
    simpa using h
  have hprev := st154_p155
  have hstep := st154_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p157 : ((21504669719593/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT154 (i+1))
      = (∑ i ∈ Finset.range 156, stT154 (i+1)) + stT154 157 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 156
    simpa using h
  have hprev := st154_p156
  have hstep := st154_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p158 : ((10820430163433/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT154 (i+1))
      = (∑ i ∈ Finset.range 157, stT154 (i+1)) + stT154 158 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 157
    simpa using h
  have hprev := st154_p157
  have hstep := st154_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p159 : ((1338110137399/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT154 (i+1))
      = (∑ i ∈ Finset.range 158, stT154 (i+1)) + stT154 159 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 158
    simpa using h
  have hprev := st154_p158
  have hstep := st154_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p160 : ((5253628391151/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT154 (i+1))
      = (∑ i ∈ Finset.range 159, stT154 (i+1)) + stT154 160 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 159
    simpa using h
  have hprev := st154_p159
  have hstep := st154_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p161 : ((5198449587597/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT154 (i+1))
      = (∑ i ∈ Finset.range 160, stT154 (i+1)) + stT154 161 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 160
    simpa using h
  have hprev := st154_p160
  have hstep := st154_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p162 : ((20931836950981/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT154 (i+1))
      = (∑ i ∈ Finset.range 161, stT154 (i+1)) + stT154 162 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 161
    simpa using h
  have hprev := st154_p161
  have hstep := st154_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p163 : ((21309880131391/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT154 (i+1))
      = (∑ i ∈ Finset.range 162, stT154 (i+1)) + stT154 163 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 162
    simpa using h
  have hprev := st154_p162
  have hstep := st154_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p164 : ((21613964576649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT154 (i+1))
      = (∑ i ∈ Finset.range 163, stT154 (i+1)) + stT154 164 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 163
    simpa using h
  have hprev := st154_p163
  have hstep := st154_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p165 : ((43194210026111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT154 (i+1))
      = (∑ i ∈ Finset.range 164, stT154 (i+1)) + stT154 165 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 164
    simpa using h
  have hprev := st154_p164
  have hstep := st154_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p166 : ((5319034561261/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT154 (i+1))
      = (∑ i ∈ Finset.range 165, stT154 (i+1)) + stT154 166 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 165
    simpa using h
  have hprev := st154_p165
  have hstep := st154_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p167 : ((5227456359981/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT154 (i+1))
      = (∑ i ∈ Finset.range 166, stT154 (i+1)) + stT154 167 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 166
    simpa using h
  have hprev := st154_p166
  have hstep := st154_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p168 : ((20787190498223/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT154 (i+1))
      = (∑ i ∈ Finset.range 167, stT154 (i+1)) + stT154 168 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 167
    simpa using h
  have hprev := st154_p167
  have hstep := st154_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p169 : ((21001313361023/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT154 (i+1))
      = (∑ i ∈ Finset.range 168, stT154 (i+1)) + stT154 169 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 168
    simpa using h
  have hprev := st154_p168
  have hstep := st154_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p170 : ((21383789487737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT154 (i+1))
      = (∑ i ∈ Finset.range 169, stT154 (i+1)) + stT154 170 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 169
    simpa using h
  have hprev := st154_p169
  have hstep := st154_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p171 : ((43282798460377/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT154 (i+1))
      = (∑ i ∈ Finset.range 170, stT154 (i+1)) + stT154 171 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 170
    simpa using h
  have hprev := st154_p170
  have hstep := st154_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p172 : ((21581153514519/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT154 (i+1))
      = (∑ i ∈ Finset.range 171, stT154 (i+1)) + stT154 172 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 171
    simpa using h
  have hprev := st154_p171
  have hstep := st154_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p173 : ((21251127047067/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT154 (i+1))
      = (∑ i ∈ Finset.range 172, stT154 (i+1)) + stT154 173 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 172
    simpa using h
  have hprev := st154_p172
  have hstep := st154_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p174 : ((41794928774659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT154 (i+1))
      = (∑ i ∈ Finset.range 173, stT154 (i+1)) + stT154 174 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 173
    simpa using h
  have hprev := st154_p173
  have hstep := st154_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p175 : ((41557054548797/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT154 (i+1))
      = (∑ i ∈ Finset.range 174, stT154 (i+1)) + stT154 175 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 174
    simpa using h
  have hprev := st154_p174
  have hstep := st154_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p176 : ((41955769190787/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT154 (i+1))
      = (∑ i ∈ Finset.range 175, stT154 (i+1)) + stT154 176 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 175
    simpa using h
  have hprev := st154_p175
  have hstep := st154_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p177 : ((42699935561441/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT154 (i+1))
      = (∑ i ∈ Finset.range 176, stT154 (i+1)) + stT154 177 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 176
    simpa using h
  have hprev := st154_p176
  have hstep := st154_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p178 : ((21630020669733/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT154 (i+1))
      = (∑ i ∈ Finset.range 177, stT154 (i+1)) + stT154 178 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 177
    simpa using h
  have hprev := st154_p177
  have hstep := st154_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p179 : ((21623003366847/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT154 (i+1))
      = (∑ i ∈ Finset.range 178, stT154 (i+1)) + stT154 179 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 178
    simpa using h
  have hprev := st154_p178
  have hstep := st154_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p180 : ((21336541440723/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT154 (i+1))
      = (∑ i ∈ Finset.range 179, stT154 (i+1)) + stT154 180 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 179
    simpa using h
  have hprev := st154_p179
  have hstep := st154_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p181 : ((41939133329481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT154 (i+1))
      = (∑ i ∈ Finset.range 180, stT154 (i+1)) + stT154 181 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 180
    simpa using h
  have hprev := st154_p180
  have hstep := st154_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p182 : ((41543308053231/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT154 (i+1))
      = (∑ i ∈ Finset.range 181, stT154 (i+1)) + stT154 182 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 181
    simpa using h
  have hprev := st154_p181
  have hstep := st154_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p183 : ((1669918869447/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT154 (i+1))
      = (∑ i ∈ Finset.range 182, stT154 (i+1)) + stT154 183 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 182
    simpa using h
  have hprev := st154_p182
  have hstep := st154_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p184 : ((42411439194323/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT154 (i+1))
      = (∑ i ∈ Finset.range 183, stT154 (i+1)) + stT154 184 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 183
    simpa using h
  have hprev := st154_p183
  have hstep := st154_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p185 : ((43093150936329/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT154 (i+1))
      = (∑ i ∈ Finset.range 184, stT154 (i+1)) + stT154 185 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 184
    simpa using h
  have hprev := st154_p184
  have hstep := st154_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p186 : ((43349281653589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT154 (i+1))
      = (∑ i ∈ Finset.range 185, stT154 (i+1)) + stT154 186 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 185
    simpa using h
  have hprev := st154_p185
  have hstep := st154_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p187 : ((43018809147067/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT154 (i+1))
      = (∑ i ∈ Finset.range 186, stT154 (i+1)) + stT154 187 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 186
    simpa using h
  have hprev := st154_p186
  have hstep := st154_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p188 : ((1322436725881/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT154 (i+1))
      = (∑ i ∈ Finset.range 187, stT154 (i+1)) + stT154 188 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 187
    simpa using h
  have hprev := st154_p187
  have hstep := st154_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p189 : ((1667707775397/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT154 (i+1))
      = (∑ i ∈ Finset.range 188, stT154 (i+1)) + stT154 189 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 188
    simpa using h
  have hprev := st154_p188
  have hstep := st154_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p190 : ((41533086543017/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT154 (i+1))
      = (∑ i ∈ Finset.range 189, stT154 (i+1)) + stT154 190 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 189
    simpa using h
  have hprev := st154_p189
  have hstep := st154_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p191 : ((41933596329201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT154 (i+1))
      = (∑ i ∈ Finset.range 190, stT154 (i+1)) + stT154 191 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 190
    simpa using h
  have hprev := st154_p190
  have hstep := st154_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p192 : ((2132179491737/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT154 (i+1))
      = (∑ i ∈ Finset.range 191, stT154 (i+1)) + stT154 192 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 191
    simpa using h
  have hprev := st154_p191
  have hstep := st154_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p193 : ((1729175558329/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT154 (i+1))
      = (∑ i ∈ Finset.range 192, stT154 (i+1)) + stT154 193 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 192
    simpa using h
  have hprev := st154_p192
  have hstep := st154_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p194 : ((8668025360029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT154 (i+1))
      = (∑ i ∈ Finset.range 193, stT154 (i+1)) + stT154 194 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 193
    simpa using h
  have hprev := st154_p193
  have hstep := st154_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p195 : ((4291423244231/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT154 (i+1))
      = (∑ i ∈ Finset.range 194, stT154 (i+1)) + stT154 195 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 194
    simpa using h
  have hprev := st154_p194
  have hstep := st154_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p196 : ((1318985357667/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT154 (i+1))
      = (∑ i ∈ Finset.range 195, stT154 (i+1)) + stT154 196 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 195
    simpa using h
  have hprev := st154_p195
  have hstep := st154_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p197 : ((20817485612749/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT154 (i+1))
      = (∑ i ∈ Finset.range 196, stT154 (i+1)) + stT154 197 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 196
    simpa using h
  have hprev := st154_p196
  have hstep := st154_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p198 : ((20763127175119/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT154 (i+1))
      = (∑ i ∈ Finset.range 197, stT154 (i+1)) + stT154 198 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 197
    simpa using h
  have hprev := st154_p197
  have hstep := st154_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p199 : ((20969712111663/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT154 (i+1))
      = (∑ i ∈ Finset.range 198, stT154 (i+1)) + stT154 199 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 198
    simpa using h
  have hprev := st154_p198
  have hstep := st154_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p200 : ((21317749684863/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT154 (i+1))
      = (∑ i ∈ Finset.range 199, stT154 (i+1)) + stT154 200 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 199
    simpa using h
  have hprev := st154_p199
  have hstep := st154_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p201 : ((1350655343343/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT154 (i+1))
      = (∑ i ∈ Finset.range 200, stT154 (i+1)) + stT154 201 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 200
    simpa using h
  have hprev := st154_p200
  have hstep := st154_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p202 : ((2710691745487/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT154 (i+1))
      = (∑ i ∈ Finset.range 201, stT154 (i+1)) + stT154 202 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 201
    simpa using h
  have hprev := st154_p201
  have hstep := st154_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p203 : ((43006894378571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT154 (i+1))
      = (∑ i ∈ Finset.range 202, stT154 (i+1)) + stT154 203 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 202
    simpa using h
  have hprev := st154_p202
  have hstep := st154_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p204 : ((42331818426371/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT154 (i+1))
      = (∑ i ∈ Finset.range 203, stT154 (i+1)) + stT154 204 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 203
    simpa using h
  have hprev := st154_p203
  have hstep := st154_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p205 : ((41713732134887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT154 (i+1))
      = (∑ i ∈ Finset.range 204, stT154 (i+1)) + stT154 205 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 204
    simpa using h
  have hprev := st154_p204
  have hstep := st154_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p206 : ((41483373062669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT154 (i+1))
      = (∑ i ∈ Finset.range 205, stT154 (i+1)) + stT154 206 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 205
    simpa using h
  have hprev := st154_p205
  have hstep := st154_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p207 : ((41759654642669/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT154 (i+1))
      = (∑ i ∈ Finset.range 206, stT154 (i+1)) + stT154 207 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 206
    simpa using h
  have hprev := st154_p206
  have hstep := st154_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p208 : ((10598198865761/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT154 (i+1))
      = (∑ i ∈ Finset.range 207, stT154 (i+1)) + stT154 208 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 207
    simpa using h
  have hprev := st154_p207
  have hstep := st154_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p209 : ((21524806591729/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT154 (i+1))
      = (∑ i ∈ Finset.range 208, stT154 (i+1)) + stT154 209 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 208
    simpa using h
  have hprev := st154_p208
  have hstep := st154_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p210 : ((43390583270803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT154 (i+1))
      = (∑ i ∈ Finset.range 209, stT154 (i+1)) + stT154 210 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 209
    simpa using h
  have hprev := st154_p209
  have hstep := st154_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p211 : ((43243862528607/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT154 (i+1))
      = (∑ i ∈ Finset.range 210, stT154 (i+1)) + stT154 211 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 210
    simpa using h
  have hprev := st154_p210
  have hstep := st154_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p212 : ((333500337209/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT154 (i+1))
      = (∑ i ∈ Finset.range 211, stT154 (i+1)) + stT154 212 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 211
    simpa using h
  have hprev := st154_p211
  have hstep := st154_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p213 : ((10501506304361/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT154 (i+1))
      = (∑ i ∈ Finset.range 212, stT154 (i+1)) + stT154 213 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 212
    simpa using h
  have hprev := st154_p212
  have hstep := st154_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p214 : ((20769337963033/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT154 (i+1))
      = (∑ i ∈ Finset.range 213, stT154 (i+1)) + stT154 214 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 213
    simpa using h
  have hprev := st154_p213
  have hstep := st154_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p215 : ((41514934998121/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT154 (i+1))
      = (∑ i ∈ Finset.range 214, stT154 (i+1)) + stT154 215 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 214
    simpa using h
  have hprev := st154_p214
  have hstep := st154_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p216 : ((20971331170949/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT154 (i+1))
      = (∑ i ∈ Finset.range 215, stT154 (i+1)) + stT154 216 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 215
    simpa using h
  have hprev := st154_p215
  have hstep := st154_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p217 : ((21305274899869/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT154 (i+1))
      = (∑ i ∈ Finset.range 216, stT154 (i+1)) + stT154 217 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 216
    simpa using h
  have hprev := st154_p216
  have hstep := st154_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p218 : ((5399428084971/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT154 (i+1))
      = (∑ i ∈ Finset.range 217, stT154 (i+1)) + stT154 218 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 217
    simpa using h
  have hprev := st154_p217
  have hstep := st154_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p219 : ((4341919228437/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT154 (i+1))
      = (∑ i ∈ Finset.range 218, stT154 (i+1)) + stT154 219 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 218
    simpa using h
  have hprev := st154_p218
  have hstep := st154_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p220 : ((4317911910317/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT154 (i+1))
      = (∑ i ∈ Finset.range 219, stT154 (i+1)) + stT154 220 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 219
    simpa using h
  have hprev := st154_p219
  have hstep := st154_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p221 : ((10647868328929/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT154 (i+1))
      = (∑ i ∈ Finset.range 220, stT154 (i+1)) + stT154 221 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 220
    simpa using h
  have hprev := st154_p220
  have hstep := st154_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p222 : ((5241496285733/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT154 (i+1))
      = (∑ i ∈ Finset.range 221, stT154 (i+1)) + stT154 222 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 221
    simpa using h
  have hprev := st154_p221
  have hstep := st154_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p223 : ((10376192436741/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT154 (i+1))
      = (∑ i ∈ Finset.range 222, stT154 (i+1)) + stT154 223 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 222
    simpa using h
  have hprev := st154_p222
  have hstep := st154_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p224 : ((4150291829223/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT154 (i+1))
      = (∑ i ∈ Finset.range 223, stT154 (i+1)) + stT154 224 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 223
    simpa using h
  have hprev := st154_p223
  have hstep := st154_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p225 : ((20961882935691/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT154 (i+1))
      = (∑ i ∈ Finset.range 224, stT154 (i+1)) + stT154 225 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 224
    simpa using h
  have hprev := st154_p224
  have hstep := st154_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p226 : ((10643761520823/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT154 (i+1))
      = (∑ i ∈ Finset.range 225, stT154 (i+1)) + stT154 226 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 225
    simpa using h
  have hprev := st154_p225
  have hstep := st154_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p227 : ((4316516618493/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT154 (i+1))
      = (∑ i ∈ Finset.range 226, stT154 (i+1)) + stT154 227 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 226
    simpa using h
  have hprev := st154_p226
  have hstep := st154_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p228 : ((10858579261931/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT154 (i+1))
      = (∑ i ∈ Finset.range 227, stT154 (i+1)) + stT154 228 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 227
    simpa using h
  have hprev := st154_p227
  have hstep := st154_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p229 : ((43267345928537/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT154 (i+1))
      = (∑ i ∈ Finset.range 228, stT154 (i+1)) + stT154 229 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 228
    simpa using h
  have hprev := st154_p228
  have hstep := st154_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p230 : ((10685039243009/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT154 (i+1))
      = (∑ i ∈ Finset.range 229, stT154 (i+1)) + stT154 230 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 229
    simpa using h
  have hprev := st154_p229
  have hstep := st154_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p231 : ((420823576169/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT154 (i+1))
      = (∑ i ∈ Finset.range 230, stT154 (i+1)) + stT154 231 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 230
    simpa using h
  have hprev := st154_p230
  have hstep := st154_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p232 : ((5196942222011/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT154 (i+1))
      = (∑ i ∈ Finset.range 231, stT154 (i+1)) + stT154 232 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 231
    simpa using h
  have hprev := st154_p231
  have hstep := st154_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p233 : ((4143287251327/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT154 (i+1))
      = (∑ i ∈ Finset.range 232, stT154 (i+1)) + stT154 233 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 232
    simpa using h
  have hprev := st154_p232
  have hstep := st154_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p234 : ((4171131997123/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT154 (i+1))
      = (∑ i ∈ Finset.range 233, stT154 (i+1)) + stT154 234 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 233
    simpa using h
  have hprev := st154_p233
  have hstep := st154_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p235 : ((21145845160939/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT154 (i+1))
      = (∑ i ∈ Finset.range 234, stT154 (i+1)) + stT154 235 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 234
    simpa using h
  have hprev := st154_p234
  have hstep := st154_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p236 : ((21466047769259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT154 (i+1))
      = (∑ i ∈ Finset.range 235, stT154 (i+1)) + stT154 236 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 235
    simpa using h
  have hprev := st154_p235
  have hstep := st154_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p237 : ((43369929078571/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT154 (i+1))
      = (∑ i ∈ Finset.range 236, stT154 (i+1)) + stT154 237 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 236
    simpa using h
  have hprev := st154_p236
  have hstep := st154_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p238 : ((4342900176257/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT154 (i+1))
      = (∑ i ∈ Finset.range 237, stT154 (i+1)) + stT154 238 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 237
    simpa using h
  have hprev := st154_p237
  have hstep := st154_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p239 : ((4308844975401/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT154 (i+1))
      = (∑ i ∈ Finset.range 238, stT154 (i+1)) + stT154 239 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 238
    simpa using h
  have hprev := st154_p238
  have hstep := st154_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p240 : ((10621849056951/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT154 (i+1))
      = (∑ i ∈ Finset.range 239, stT154 (i+1)) + stT154 240 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 239
    simpa using h
  have hprev := st154_p239
  have hstep := st154_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p241 : ((2093301088629/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT154 (i+1))
      = (∑ i ∈ Finset.range 240, stT154 (i+1)) + stT154 241 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 240
    simpa using h
  have hprev := st154_p240
  have hstep := st154_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p242 : ((8293747456131/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT154 (i+1))
      = (∑ i ∈ Finset.range 241, stT154 (i+1)) + stT154 242 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 241
    simpa using h
  have hprev := st154_p241
  have hstep := st154_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p243 : ((4144874490199/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT154 (i+1))
      = (∑ i ∈ Finset.range 242, stT154 (i+1)) + stT154 243 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 242
    simpa using h
  have hprev := st154_p242
  have hstep := st154_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p244 : ((20905444654291/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT154 (i+1))
      = (∑ i ∈ Finset.range 243, stT154 (i+1)) + stT154 244 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 243
    simpa using h
  have hprev := st154_p243
  have hstep := st154_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p245 : ((21206621022707/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT154 (i+1))
      = (∑ i ∈ Finset.range 244, stT154 (i+1)) + stT154 245 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 244
    simpa using h
  have hprev := st154_p244
  have hstep := st154_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p246 : ((21512292490447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT154 (i+1))
      = (∑ i ∈ Finset.range 245, stT154 (i+1)) + stT154 246 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 245
    simpa using h
  have hprev := st154_p245
  have hstep := st154_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p247 : ((21706924766923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT154 (i+1))
      = (∑ i ∈ Finset.range 246, stT154 (i+1)) + stT154 247 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 246
    simpa using h
  have hprev := st154_p246
  have hstep := st154_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p248 : ((21718383341923/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT154 (i+1))
      = (∑ i ∈ Finset.range 247, stT154 (i+1)) + stT154 248 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 247
    simpa using h
  have hprev := st154_p247
  have hstep := st154_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p249 : ((43087551888871/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT154 (i+1))
      = (∑ i ∈ Finset.range 248, stT154 (i+1)) + stT154 249 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 248
    simpa using h
  have hprev := st154_p248
  have hstep := st154_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_p250 : ((42497861298679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT154 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT154 (i+1))
      = (∑ i ∈ Finset.range 249, stT154 (i+1)) + stT154 250 := by
    have h := Finset.sum_range_succ (fun i => stT154 (i+1)) 249
    simpa using h
  have hprev := st154_p249
  have hstep := st154_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st154_s250 :
    |Real.sin (((154 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))
      - ((180801/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := 6929017/10000000) (δ := 1933/250000000) (ψ := -696637/1000000) 154 135
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 154`** (evaluated boundary). -/
theorem station_154_sign : 0 < hardyG ((((154:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 154 250 (by norm_num) (by norm_num)
    ((-696637/1000000 : ℚ) : ℝ)
  have hchain := st154_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT154 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((154 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-696637/1000000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st154_c250
  have hsinb := abs_le.mp st154_s250
  have hbdy_lo : ((-4366181104219/118581250000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((154 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ))) / 2
          - ((((154:ℕ)):ℝ))
            * Real.sin (((154 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-696637/1000000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((154:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((154:ℝ) * Real.log (250:ℝ) - ((-696637/1000000 : ℚ) : ℝ))) / 2
        - ((154:ℝ)) * Real.sin ((154:ℝ) * Real.log (250:ℝ) - ((-696637/1000000 : ℚ) : ℝ))
        ≥ ((-55228267/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((154:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hEloneg : ((-55228267/1000000 : ℚ) : ℝ) ≤ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (79057/1250000)
          * ((-55228267/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((-55228267/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((154:ℕ)):ℝ))+1) * (((((154:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((17013777913/31250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((42497861298679/10000000000000 : ℚ) : ℝ) + ((-4366181104219/118581250000000 : ℚ) : ℝ)
      - ((17013777913/31250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-696637/1000000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((154:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-696637/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((154:ℕ)):ℝ)))).re
      - Real.sin ((-696637/1000000 : ℚ) : ℝ)
        * (riemannZeta (line ((((154:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((154:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((154:ℕ)):ℝ))
      = (((((154:ℕ)):ℝ)) * (Real.log ((((154:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((154:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_154
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
  have hθwin : |(((-696637/1000000 : ℚ) : ℝ) + ((27:ℤ)) * (2*Real.pi)) - theta ((((154:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((154:ℕ)):ℝ)))
    (φ := ((-696637/1000000 : ℚ) : ℝ) + ((27:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-696637/1000000 : ℚ)) : ℝ) 27).1,
    (cos_sin_shift (((-696637/1000000 : ℚ)) : ℝ) 27).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_154_sign
end AxiomAudit
