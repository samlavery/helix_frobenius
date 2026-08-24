import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 177` (rung-199.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT177 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((177 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-393717/500000 : ℚ) : ℝ))

theorem st177_c1 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((352833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 393717/2000000) (δ := 1/1000000000) (ψ := -393717/500000) 177 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t1 : ((44101/62500 : ℚ) : ℝ) ≤ stT177 1 := by
  have hc : ((44101/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44101/62500 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((44101/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c2 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-579757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2736533/5000000) (δ := 1809/200000000) (ψ := -393717/500000) 177 20
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t2 : ((-1024963680969/2500000000000 : ℚ) : ℝ) ≤ stT177 2 := by
  have hc : ((-579807/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).2
  have h0 : (0:ℝ) ≤ ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1024963680969/2500000000000 : ℚ) : ℝ)
      = ((1767767/2500000 : ℚ) : ℝ) * ((-579807/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c3 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((894691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289411/2500000) (δ := 8979/1000000000) (ψ := -393717/500000) 177 31
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t3 : ((2582605801391/5000000000000 : ℚ) : ℝ) ≤ stT177 3 := by
  have hc : ((894641/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).1
  have hw2 : ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2582605801391/5000000000000 : ℚ) : ℝ)
      = ((2886751/5000000 : ℚ) : ℝ) * ((894641/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c4 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((87621/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2793267/10000000) (δ := 9021/1000000000) (ψ := -393717/500000) 177 39
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t4 : ((87611/400000 : ℚ) : ℝ) ≤ stT177 4 := by
  have hc : ((87611/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((87611/400000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((87611/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c5 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-19487/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7286531/10000000) (δ := 357/40000000) (ψ := -393717/500000) 177 45
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t5 : ((-340441353/781250000 : ℚ) : ℝ) ≤ stT177 5 := by
  have hc : ((-609/625 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).2
  have h0 : (0:ℝ) ≤ ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-340441353/781250000 : ℚ) : ℝ)
      = ((559017/1250000 : ℚ) : ℝ) * ((-609/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c6 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-161841/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1256797/2000000) (δ := 2217/250000000) (ψ := -393717/500000) 177 51
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t6 : ((-660753956033/2000000000000 : ℚ) : ℝ) ≤ stT177 6 := by
  have hc : ((-161851/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-660753956033/2000000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-161851/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c7 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((93531/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -904153/10000000) (δ := 2249/250000000) (ψ := -393717/500000) 177 55
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t7 : ((44186873093/125000000000 : ℚ) : ℝ) ≤ stT177 7 := by
  have hc : ((46763/50000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44186873093/125000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((46763/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c8 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-284561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2324181/5000000) (δ := 4439/500000000) (ψ := -393717/500000) 177 59
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t8 : ((-503125933637/5000000000000 : ℚ) : ℝ) ≤ stT177 8 := by
  have hc : ((-284611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).2
  have h0 : (0:ℝ) ≤ ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-503125933637/5000000000000 : ℚ) : ℝ)
      = ((1767767/5000000 : ℚ) : ℝ) * ((-284611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c9 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((495199/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 173363/5000000) (δ := 8947/1000000000) (ψ := -393717/500000) 177 62
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t9 : ((825289917471/2500000000000 : ℚ) : ℝ) ≤ stT177 9 := by
  have hc : ((247587/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((825289917471/2500000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((247587/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c10 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((39923/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -155143/10000000) (δ := 1787/200000000) (ψ := -393717/500000) 177 65
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t10 : ((126241260117/400000000000 : ℚ) : ℝ) ≤ stT177 10 := by
  have hc : ((39921/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((126241260117/400000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((39921/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c11 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-453699/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5104269/10000000) (δ := 889/100000000) (ψ := -393717/500000) 177 68
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t11 : ((-684052481193/5000000000000 : ℚ) : ℝ) ≤ stT177 11 := by
  have hc : ((-453749/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-684052481193/5000000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-453749/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c12 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((350877/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1982349/10000000) (δ := 1113/125000000) (ψ := -393717/500000) 177 70
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t12 : ((253205590463/1250000000000 : ℚ) : ℝ) ≤ stT177 12 := by
  have hc : ((87713/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).1
  have hw2 : ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2886751/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((253205590463/1250000000000 : ℚ) : ℝ)
      = ((2886751/10000000 : ℚ) : ℝ) * ((87713/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c13 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-366707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5985317/10000000) (δ := 1777/200000000) (ψ := -393717/500000) 177 72
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t13 : ((-254282892183/1250000000000 : ℚ) : ℝ) ≤ stT177 13 := by
  have hc : ((-91683/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-254282892183/1250000000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-91683/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c14 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-980713/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7362181/10000000) (δ := 9033/1000000000) (ψ := -393717/500000) 177 74
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t14 : ((-2621199943719/10000000000000 : ℚ) : ℝ) ≤ stT177 14 := by
  have hc : ((-980763/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).2
  have h0 : (0:ℝ) ≤ ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2621199943719/10000000000000 : ℚ) : ℝ)
      = ((2672613/10000000 : ℚ) : ℝ) * ((-980763/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c15 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-851819/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1618903/2500000) (δ := 2239/250000000) (ψ := -393717/500000) 177 76
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t15 : ((-2199516387441/10000000000000 : ℚ) : ℝ) ≤ stT177 15 := by
  have hc : ((-851869/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2199516387441/10000000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-851869/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c16 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((123293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 904493/2500000) (δ := 4431/500000000) (ψ := -393717/500000) 177 78
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t16 : ((123243/4000000 : ℚ) : ℝ) ≤ stT177 16 := by
  have hc : ((123243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123243/4000000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((123243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c17 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((92543/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -971569/10000000) (δ := 2219/250000000) (ψ := -393717/500000) 177 80
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t17 : ((28054699191/125000000000 : ℚ) : ℝ) ≤ stT177 17 := by
  have hc : ((46269/50000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28054699191/125000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((46269/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c18 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-954257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -886863/1250000) (δ := 9013/1000000000) (ψ := -393717/500000) 177 82
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t18 : ((-2249323548061/10000000000000 : ℚ) : ℝ) ≤ stT177 18 := by
  have hc : ((-954307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).2
  have h0 : (0:ℝ) ≤ ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2249323548061/10000000000000 : ℚ) : ℝ)
      = ((2357023/10000000 : ℚ) : ℝ) * ((-954307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c19 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((900991/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1121869/10000000) (δ := 4453/500000000) (ψ := -393717/500000) 177 83
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t19 : ((2066900101737/10000000000000 : ℚ) : ℝ) ≤ stT177 19 := by
  have hc : ((900941/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2066900101737/10000000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((900941/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c20 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-124339/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1899193/2500000) (δ := 557/62500000) (ψ := -393717/500000) 177 85
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t20 : ((-278044434477/1250000000000 : ℚ) : ℝ) ≤ stT177 20 := by
  have hc : ((-497381/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).2
  have h0 : (0:ℝ) ≤ ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278044434477/1250000000000 : ℚ) : ℝ)
      = ((559017/2500000 : ℚ) : ℝ) * ((-497381/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c21 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((96721/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -13399/78125) (δ := 2221/250000000) (ψ := -393717/500000) 177 86
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t21 : ((422097599451/2500000000000 : ℚ) : ℝ) ≤ stT177 21 := by
  have hc : ((386859/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).1
  have hw2 : ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422097599451/2500000000000 : ℚ) : ℝ)
      = ((1091089/5000000 : ℚ) : ℝ) * ((386859/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c22 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((301219/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 632413/2000000) (δ := 4463/500000000) (ψ := -393717/500000) 177 87
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t22 : ((642094416183/10000000000000 : ℚ) : ℝ) ≤ stT177 22 := by
  have hc : ((301169/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).1
  have hw2 : ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2132007/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((642094416183/10000000000000 : ℚ) : ℝ)
      = ((2132007/10000000 : ℚ) : ℝ) * ((301169/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c23 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-38307/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7124023/10000000) (δ := 887/100000000) (ψ := -393717/500000) 177 88
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t23 : ((-15975963961/80000000000 : ℚ) : ℝ) ≤ stT177 23 := by
  have hc : ((-38309/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).2
  have h0 : (0:ℝ) ≤ ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-15975963961/80000000000 : ℚ) : ℝ)
      = ((417029/2000000 : ℚ) : ℝ) * ((-38309/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c24 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-115051/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -68241/125000) (δ := 1131/125000000) (ψ := -393717/500000) 177 90
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t24 : ((-117433672881/1000000000000 : ℚ) : ℝ) ≤ stT177 24 := by
  have hc : ((-115061/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-117433672881/1000000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-115061/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c25 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((80867/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3103509/10000000) (δ := 2237/250000000) (ψ := -393717/500000) 177 91
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t25 : ((161709/2500000 : ℚ) : ℝ) ≤ stT177 25 := by
  have hc : ((161709/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161709/2500000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((161709/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c26 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((208769/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -182039/1250000) (δ := 4481/500000000) (ψ := -393717/500000) 177 92
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t26 : ((818810212593/5000000000000 : ℚ) : ℝ) ≤ stT177 26 := by
  have hc : ((417513/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).1
  have hw2 : ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1961161/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((818810212593/5000000000000 : ℚ) : ℝ)
      = ((1961161/10000000 : ℚ) : ℝ) * ((417513/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c27 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((982811/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -464193/10000000) (δ := 4467/500000000) (ψ := -393717/500000) 177 93
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t27 : ((3782647089/20000000000 : ℚ) : ℝ) ≤ stT177 27 := by
  have hc : ((982761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).1
  have hw2 : ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3782647089/20000000000 : ℚ) : ℝ)
      = ((3849/20000 : ℚ) : ℝ) * ((982761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c28 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((199899/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -79449/10000000) (δ := 8927/1000000000) (ψ := -393717/500000) 177 94
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t28 : ((188877314879/1000000000000 : ℚ) : ℝ) ≤ stT177 28 := by
  have hc : ((199889/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((188877314879/1000000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((199889/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c29 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((994617/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -32439/1250000) (δ := 8919/1000000000) (ψ := -393717/500000) 177 95
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t29 : ((1846864174351/10000000000000 : ℚ) : ℝ) ≤ stT177 29 := by
  have hc : ((994567/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1846864174351/10000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((994567/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c30 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((926263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -966061/10000000) (δ := 8991/1000000000) (ψ := -393717/500000) 177 96
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t30 : ((1691025048833/10000000000000 : ℚ) : ℝ) ≤ stT177 30 := by
  have hc : ((926213/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).1
  have hw2 : ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1825741/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1691025048833/10000000000000 : ℚ) : ℝ)
      = ((1825741/10000000 : ℚ) : ℝ) * ((926213/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c31 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((648033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1082247/5000000) (δ := 1781/200000000) (ψ := -393717/500000) 177 97
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t31 : ((1163811811099/10000000000000 : ℚ) : ℝ) ≤ stT177 31 := by
  have hc : ((647983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).1
  have hw2 : ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1796053/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1163811811099/10000000000000 : ℚ) : ℝ)
      = ((1796053/10000000 : ℚ) : ℝ) * ((647983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c32 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((20661/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3823657/10000000) (δ := 1801/200000000) (ψ := -393717/500000) 177 98
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t32 : ((4559952397/625000000000 : ℚ) : ℝ) ≤ stT177 32 := by
  have hc : ((5159/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4559952397/625000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((5159/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c33 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-714059/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1478797/2500000) (δ := 8991/1000000000) (ψ := -393717/500000) 177 99
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t33 : ((-1243104522693/10000000000000 : ℚ) : ℝ) ≤ stT177 33 := by
  have hc : ((-714109/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).2
  have h0 : (0:ℝ) ≤ ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1243104522693/10000000000000 : ℚ) : ℝ)
      = ((1740777/10000000 : ℚ) : ℝ) * ((-714109/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c34 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-487543/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1458953/2000000) (δ := 557/62500000) (ψ := -393717/500000) 177 99
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t34 : ((-26130384189/156250000000 : ℚ) : ℝ) ≤ stT177 34 := by
  have hc : ((-30473/31250 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).2
  have h0 : (0:ℝ) ≤ ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26130384189/156250000000 : ℚ) : ℝ)
      = ((857493/5000000 : ℚ) : ℝ) * ((-30473/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c35 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-48371/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 441377/1000000) (δ := 1123/125000000) (ψ := -393717/500000) 177 100
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t35 : ((-163566131003/5000000000000 : ℚ) : ℝ) ≤ stT177 35 := by
  have hc : ((-96767/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).2
  have h0 : (0:ℝ) ≤ ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-163566131003/5000000000000 : ℚ) : ℝ)
      = ((1690309/10000000 : ℚ) : ℝ) * ((-96767/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c36 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((446107/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 117143/1000000) (δ := 561/62500000) (ψ := -393717/500000) 177 101
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t36 : ((185867425653/1250000000000 : ℚ) : ℝ) ≤ stT177 36 := by
  have hc : ((223041/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((185867425653/1250000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((223041/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c37 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((22777/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96499/400000) (δ := 4517/500000000) (ψ := -393717/500000) 177 102
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t37 : ((1497673979/16000000000 : ℚ) : ℝ) ≤ stT177 37 := by
  have hc : ((911/1600 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1497673979/16000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((911/1600 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c38 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-817529/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -78997/125000) (δ := 8941/1000000000) (ψ := -393717/500000) 177 103
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t38 : ((-265257783497/2000000000000 : ℚ) : ℝ) ≤ stT177 38 := by
  have hc : ((-817579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).2
  have h0 : (0:ℝ) ≤ ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-265257783497/2000000000000 : ℚ) : ℝ)
      = ((324443/2000000 : ℚ) : ℝ) * ((-817579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c39 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-95703/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5174399/10000000) (δ := 9041/1000000000) (ψ := -393717/500000) 177 103
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t39 : ((-76631752033/1000000000000 : ℚ) : ℝ) ≤ stT177 39 := by
  have hc : ((-95713/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).2
  have h0 : (0:ℝ) ≤ ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-76631752033/1000000000000 : ℚ) : ℝ)
      = ((800641/5000000 : ℚ) : ℝ) * ((-95713/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c40 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((964349/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 334781/5000000) (δ := 2237/250000000) (ψ := -393717/500000) 177 104
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t40 : ((762344896131/5000000000000 : ℚ) : ℝ) ≤ stT177 40 := by
  have hc : ((964299/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((762344896131/5000000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((964299/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c41 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-73907/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2055963/5000000) (δ := 1771/200000000) (ψ := -393717/500000) 177 105
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t41 : ((-57750728633/5000000000000 : ℚ) : ℝ) ≤ stT177 41 := by
  have hc : ((-73957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-57750728633/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-73957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c42 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-433639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3275631/5000000) (δ := 1771/200000000) (ψ := -393717/500000) 177 105
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t42 : ((-653474899/4882812500 : ℚ) : ℝ) ≤ stT177 42 := by
  have hc : ((-13552/15625 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-653474899/4882812500 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-13552/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c43 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((876517/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 251109/2000000) (δ := 8863/1000000000) (ψ := -393717/500000) 177 106
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t43 : ((267319805599/2000000000000 : ℚ) : ℝ) ≤ stT177 43 := by
  have hc : ((876467/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).1
  have hw2 : ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((304997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267319805599/2000000000000 : ℚ) : ℝ)
      = ((304997/2000000 : ℚ) : ℝ) * ((876467/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c44 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-140563/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -855913/2000000) (δ := 9033/1000000000) (ψ := -393717/500000) 177 107
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t44 : ((-211982112441/10000000000000 : ℚ) : ℝ) ≤ stT177 44 := by
  have hc : ((-140613/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).2
  have h0 : (0:ℝ) ≤ ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-211982112441/10000000000000 : ℚ) : ℝ)
      = ((1507557/10000000 : ℚ) : ℝ) * ((-140613/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c45 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-320217/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5664649/10000000) (δ := 9033/1000000000) (ψ := -393717/500000) 177 107
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t45 : ((-29836787019/312500000000 : ℚ) : ℝ) ≤ stT177 45 := by
  have hc : ((-160121/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).2
  have h0 : (0:ℝ) ≤ ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29836787019/312500000000 : ℚ) : ℝ)
      = ((186339/1250000 : ℚ) : ℝ) * ((-160121/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c46 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((991939/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317651/10000000) (δ := 4513/500000000) (ψ := -393717/500000) 177 108
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t46 : ((1462459987491/10000000000000 : ℚ) : ℝ) ≤ stT177 46 := by
  have hc : ((991889/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1462459987491/10000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((991889/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c47 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-171751/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1627269/2500000) (δ := 2221/250000000) (ψ := -393717/500000) 177 109
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t47 : ((-5010783653/40000000000 : ℚ) : ℝ) ≤ stT177 47 := by
  have hc : ((-171761/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5010783653/40000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-171761/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c48 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((433141/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2807053/10000000) (δ := 9019/1000000000) (ψ := -393717/500000) 177 109
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t48 : ((5000901777/80000000000 : ℚ) : ℝ) ≤ stT177 48 := by
  have hc : ((433091/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).1
  have hw2 : ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5000901777/80000000000 : ℚ) : ℝ)
      = ((11547/80000 : ℚ) : ℝ) * ((433091/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c49 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((11999/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1888457/5000000) (δ := 557/62500000) (ψ := -393717/500000) 177 110
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t49 : ((17127137719/2000000000000 : ℚ) : ℝ) ≤ stT177 49 := by
  have hc : ((11989/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((17127137719/2000000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((11989/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c50 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-94889/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 206513/400000) (δ := 557/62500000) (ψ := -393717/500000) 177 110
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t50 : ((-67103747193/1000000000000 : ℚ) : ℝ) ≤ stT177 50 := by
  have hc : ((-94899/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).2
  have h0 : (0:ℝ) ≤ ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67103747193/1000000000000 : ℚ) : ℝ)
      = ((707107/5000000 : ℚ) : ℝ) * ((-94899/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c51 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((378203/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -222811/1250000) (δ := 1801/200000000) (ψ := -393717/500000) 177 111
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t51 : ((6619438623/62500000000 : ℚ) : ℝ) ≤ stT177 51 := by
  have hc : ((189089/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).1
  have hw2 : ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6619438623/62500000000 : ℚ) : ℝ)
      = ((35007/250000 : ℚ) : ℝ) * ((189089/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c52 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-914071/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3405011/5000000) (δ := 4499/500000000) (ψ := -393717/500000) 177 111
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t52 : ((-1267658210871/10000000000000 : ℚ) : ℝ) ≤ stT177 52 := by
  have hc : ((-914121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).2
  have h0 : (0:ℝ) ≤ ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1267658210871/10000000000000 : ℚ) : ℝ)
      = ((1386751/10000000 : ℚ) : ℝ) * ((-914121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c53 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((491223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -469113/10000000) (δ := 4453/500000000) (ψ := -393717/500000) 177 112
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t53 : ((67471202879/500000000000 : ℚ) : ℝ) ≤ stT177 53 := by
  have hc : ((245599/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((67471202879/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((245599/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c54 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-199957/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7802141/10000000) (δ := 8897/1000000000) (ψ := -393717/500000) 177 112
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t54 : ((-68030173169/500000000000 : ℚ) : ℝ) ≤ stT177 54 := by
  have hc : ((-199967/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-68030173169/500000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-199967/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c55 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((19927/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42731/2000000) (δ := 9013/1000000000) (ψ := -393717/500000) 177 113
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t55 : ((13434099237/100000000000 : ℚ) : ℝ) ≤ stT177 55 := by
  have hc : ((9963/10000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).1
  have hw2 : ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1348399/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13434099237/100000000000 : ℚ) : ℝ)
      = ((1348399/10000000 : ℚ) : ℝ) * ((9963/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c56 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-991149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3760561/5000000) (δ := 451/50000000) (ψ := -393717/500000) 177 114
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t56 : ((-1324546162093/10000000000000 : ℚ) : ℝ) ≤ stT177 56 := by
  have hc : ((-991199/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).2
  have h0 : (0:ℝ) ≤ ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1324546162093/10000000000000 : ℚ) : ℝ)
      = ((1336307/10000000 : ℚ) : ℝ) * ((-991199/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c57 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((39691/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 310951/10000000) (δ := 451/50000000) (ψ := -393717/500000) 177 114
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t57 : ((13142337637/100000000000 : ℚ) : ℝ) ≤ stT177 57 := by
  have hc : ((39689/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).1
  have hw2 : ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((13142337637/100000000000 : ℚ) : ℝ)
      = ((331133/2500000 : ℚ) : ℝ) * ((39689/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c58 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-249533/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7701141/10000000) (δ := 8927/1000000000) (ψ := -393717/500000) 177 115
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t58 : ((-131067784783/1000000000000 : ℚ) : ℝ) ≤ stT177 58 := by
  have hc : ((-499091/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).2
  have h0 : (0:ℝ) ≤ ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-131067784783/1000000000000 : ℚ) : ℝ)
      = ((262613/2000000 : ℚ) : ℝ) * ((-499091/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c59 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((499251/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -136869/10000000) (δ := 8927/1000000000) (ψ := -393717/500000) 177 115
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t59 : ((324968418957/2500000000000 : ℚ) : ℝ) ≤ stT177 59 := by
  have hc : ((249613/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((324968418957/2500000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((249613/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c60 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-975573/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7300273/10000000) (δ := 9027/1000000000) (ψ := -393717/500000) 177 115
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t60 : ((-251904882977/2000000000000 : ℚ) : ℝ) ≤ stT177 60 := by
  have hc : ((-975623/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251904882977/2000000000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-975623/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c61 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((45293/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -43739/400000) (δ := 4517/500000000) (ψ := -393717/500000) 177 116
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t61 : ((7248563363/62500000000 : ℚ) : ℝ) ≤ stT177 61 := by
  have hc : ((90581/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7248563363/62500000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((90581/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c62 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-764279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1525449/2500000) (δ := 4467/500000000) (ψ := -393717/500000) 177 116
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t62 : ((-485349679329/5000000000000 : ℚ) : ℝ) ≤ stT177 62 := by
  have hc : ((-764329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-485349679329/5000000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-764329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c63 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((21261/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -252599/1000000) (δ := 4521/500000000) (ψ := -393717/500000) 177 117
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t63 : ((26783810179/400000000000 : ℚ) : ℝ) ≤ stT177 63 := by
  have hc : ((21259/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26783810179/400000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((21259/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c64 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-204797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 555329/1250000) (δ := 8961/1000000000) (ψ := -393717/500000) 177 117
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t64 : ((-256058954847/10000000000000 : ℚ) : ℝ) ≤ stT177 64 := by
  have hc : ((-204847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-256058954847/10000000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-204847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c65 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-47483/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2202361/5000000) (δ := 9049/1000000000) (ψ := -393717/500000) 177 118
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t65 : ((-29455474217/1250000000000 : ℚ) : ℝ) ≤ stT177 65 := by
  have hc : ((-94991/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29455474217/1250000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-94991/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c66 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((294709/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1175573/5000000) (δ := 4477/500000000) (ψ := -393717/500000) 177 118
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t66 : ((45341332647/625000000000 : ℚ) : ℝ) ≤ stT177 66 := by
  have hc : ((73671/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((45341332647/625000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((73671/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c67 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-895797/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3351273/5000000) (δ := 2239/250000000) (ψ := -393717/500000) 177 119
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t67 : ((-218890360133/2000000000000 : ℚ) : ℝ) ≤ stT177 67 := by
  have hc : ((-895847/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-218890360133/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-895847/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c68 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((39931/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -29373/2000000) (δ := 9047/1000000000) (ψ := -393717/500000) 177 119
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t68 : ((24210509931/200000000000 : ℚ) : ℝ) ≤ stT177 68 := by
  have hc : ((39929/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24210509931/200000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((39929/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c69 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-815993/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 394569/625000) (δ := 9047/1000000000) (ψ := -393717/500000) 177 119
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t69 : ((-982400709937/10000000000000 : ℚ) : ℝ) ≤ stT177 69 := by
  have hc : ((-816043/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-982400709937/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-816043/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c70 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((351949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3027859/10000000) (δ := 8863/1000000000) (ψ := -393717/500000) 177 120
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t70 : ((105149884493/2500000000000 : ℚ) : ℝ) ≤ stT177 70 := by
  have hc : ((351899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((105149884493/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((351899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c71 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((267951/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1624413/5000000) (δ := 113/12500000) (ψ := -393717/500000) 177 120
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t71 : ((317939816681/10000000000000 : ℚ) : ℝ) ≤ stT177 71 := by
  have hc : ((267901/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).1
  have hw2 : ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1186781/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((317939816681/10000000000000 : ℚ) : ℝ)
      = ((1186781/10000000 : ℚ) : ℝ) * ((267901/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c72 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-805953/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6270199/10000000) (δ := 887/100000000) (ψ := -393717/500000) 177 121
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t72 : ((-59367762971/625000000000 : ℚ) : ℝ) ≤ stT177 72 := by
  have hc : ((-806003/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).2
  have h0 : (0:ℝ) ≤ ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59367762971/625000000000 : ℚ) : ℝ)
      = ((73657/625000 : ℚ) : ℝ) * ((-806003/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c73 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((997779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -20833/1250000) (δ := 8933/1000000000) (ψ := -393717/500000) 177 121
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t73 : ((1167752996619/10000000000000 : ℚ) : ℝ) ≤ stT177 73 := by
  have hc : ((997729/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).1
  have hw2 : ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1170411/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1167752996619/10000000000000 : ℚ) : ℝ)
      = ((1170411/10000000 : ℚ) : ℝ) * ((997729/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c74 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-696659/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2926907/5000000) (δ := 8933/1000000000) (ψ := -393717/500000) 177 121
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t74 : ((-809908188193/10000000000000 : ℚ) : ℝ) ≤ stT177 74 := by
  have hc : ((-696709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).2
  have h0 : (0:ℝ) ≤ ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-809908188193/10000000000000 : ℚ) : ℝ)
      = ((1162477/10000000 : ℚ) : ℝ) * ((-696709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c75 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((2513/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3914427/10000000) (δ := 8977/1000000000) (ψ := -393717/500000) 177 122
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t75 : ((3591117/6250000000 : ℚ) : ℝ) ≤ stT177 75 := by
  have hc : ((311/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).1
  have hw2 : ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11547/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3591117/6250000000 : ℚ) : ℝ)
      = ((11547/100000 : ℚ) : ℝ) * ((311/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c76 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((711877/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 973287/5000000) (δ := 8977/1000000000) (ψ := -393717/500000) 177 122
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t76 : ((408260545753/5000000000000 : ℚ) : ℝ) ≤ stT177 76 := by
  have hc : ((711827/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((408260545753/5000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((711827/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c77 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-99879/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3865489/5000000) (δ := 8877/1000000000) (ψ := -393717/500000) 177 122
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t77 : ((-14228550713/125000000000 : ℚ) : ℝ) ≤ stT177 77 := by
  have hc : ((-24971/25000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14228550713/125000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-24971/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c78 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((154049/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2267231/10000000) (δ := 4459/500000000) (ψ := -393717/500000) 177 123
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t78 : ((348823972221/5000000000000 : ℚ) : ℝ) ≤ stT177 78 := by
  have hc : ((308073/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((348823972221/5000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((308073/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c79 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((44209/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3369777/10000000) (δ := 1797/200000000) (ψ := -393717/500000) 177 123
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t79 : ((49727720313/2000000000000 : ℚ) : ℝ) ≤ stT177 79 := by
  have hc : ((44199/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).1
  have hw2 : ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1125087/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49727720313/2000000000000 : ℚ) : ℝ)
      = ((1125087/10000000 : ℚ) : ℝ) * ((44199/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c80 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-907809/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1693017/2500000) (δ := 9011/1000000000) (ψ := -393717/500000) 177 124
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t80 : ((-507508614603/5000000000000 : ℚ) : ℝ) ≤ stT177 80 := by
  have hc : ((-907859/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-507508614603/5000000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-907859/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c81 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((872723/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1275111/10000000) (δ := 281/31250000) (ψ := -393717/500000) 177 124
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t81 : ((969636569703/10000000000000 : ℚ) : ℝ) ≤ stT177 81 := by
  have hc : ((872673/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((969636569703/10000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((872673/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c82 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-90841/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 519301/1250000) (δ := 2223/250000000) (ψ := -393717/500000) 177 124
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t82 : ((-25093096389/2500000000000 : ℚ) : ℝ) ≤ stT177 82 := by
  have hc : ((-90891/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25093096389/2500000000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-90891/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c83 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-78651/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1547459/2500000) (δ := 1113/125000000) (ψ := -393717/500000) 177 125
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t83 : ((-1349003247/15625000000 : ℚ) : ℝ) ≤ stT177 83 := by
  have hc : ((-2458/3125 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).2
  have h0 : (0:ℝ) ≤ ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1349003247/15625000000 : ℚ) : ℝ)
      = ((1097643/10000000 : ℚ) : ℝ) * ((-2458/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c84 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((234311/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -890389/10000000) (δ := 17899/1000000000) (ψ := -393717/500000) 177 125
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t84 : ((511281032133/5000000000000 : ℚ) : ℝ) ≤ stT177 84 := by
  have hc : ((468597/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).1
  have hw2 : ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1091089/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((511281032133/5000000000000 : ℚ) : ℝ)
      = ((1091089/10000000 : ℚ) : ℝ) * ((468597/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c85 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-2087/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 869271/2000000) (δ := 8999/1000000000) (ψ := -393717/500000) 177 125
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t85 : ((-18114789753/1000000000000 : ℚ) : ℝ) ≤ stT177 85 := by
  have hc : ((-16701/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).2
  have h0 : (0:ℝ) ≤ ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18114789753/1000000000000 : ℚ) : ℝ)
      = ((1084653/10000000 : ℚ) : ℝ) * ((-16701/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c86 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-392797/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6186129/10000000) (δ := 8997/1000000000) (ψ := -393717/500000) 177 126
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t86 : ((-26474435101/312500000000 : ℚ) : ℝ) ≤ stT177 86 := by
  have hc : ((-196411/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26474435101/312500000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-196411/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c87 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((454863/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -107043/1000000) (δ := 4503/500000000) (ψ := -393717/500000) 177 126
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t87 : ((15238664933/156250000000 : ℚ) : ℝ) ≤ stT177 87 := by
  have hc : ((227419/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).1
  have hw2 : ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((67007/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15238664933/156250000000 : ℚ) : ℝ)
      = ((67007/625000 : ℚ) : ℝ) * ((227419/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c88 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-23909/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3986769/10000000) (δ := 8997/1000000000) (ψ := -393717/500000) 177 126
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t88 : ((-6385097459/2500000000000 : ℚ) : ℝ) ≤ stT177 88 := by
  have hc : ((-23959/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).2
  have h0 : (0:ℝ) ≤ ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-6385097459/2500000000000 : ℚ) : ℝ)
      = ((266501/2500000 : ℚ) : ℝ) * ((-23959/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c89 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-899083/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1344233/2000000) (δ := 8913/1000000000) (ψ := -393717/500000) 177 127
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t89 : ((-476539590867/5000000000000 : ℚ) : ℝ) ≤ stT177 89 := by
  have hc : ((-899133/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-476539590867/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-899133/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c90 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((151569/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88849/500000) (δ := 889/100000000) (ψ := -393717/500000) 177 127
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t90 : ((39939282357/500000000000 : ℚ) : ℝ) ≤ stT177 90 := by
  have hc : ((151559/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((39939282357/500000000000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((151559/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c91 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((320033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3112579/10000000) (δ := 17813/1000000000) (ψ := -393717/500000) 177 127
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t91 : ((83858264793/2500000000000 : ℚ) : ℝ) ≤ stT177 91 := by
  have hc : ((319983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).1
  have hw2 : ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((262071/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((83858264793/2500000000000 : ℚ) : ℝ)
      = ((262071/2500000 : ℚ) : ℝ) * ((319983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c92 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-999283/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -96991/125000) (δ := 8883/1000000000) (ψ := -393717/500000) 177 128
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t92 : ((-1041877603809/10000000000000 : ℚ) : ℝ) ≤ stT177 92 := by
  have hc : ((-999333/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).2
  have h0 : (0:ℝ) ≤ ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1041877603809/10000000000000 : ℚ) : ℝ)
      = ((1042573/10000000 : ℚ) : ℝ) * ((-999333/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c93 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((37149/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2975457/10000000) (δ := 8983/1000000000) (ψ := -393717/500000) 177 128
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t93 : ((4814563493/125000000000 : ℚ) : ℝ) ≤ stT177 93 := by
  have hc : ((4643/12500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4814563493/125000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((4643/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c94 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((38149/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 878607/5000000) (δ := 451/50000000) (ψ := -393717/500000) 177 128
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t94 : ((78690202353/1000000000000 : ℚ) : ℝ) ≤ stT177 94 := by
  have hc : ((76293/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).1
  have hw2 : ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1031421/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78690202353/1000000000000 : ℚ) : ℝ)
      = ((1031421/10000000 : ℚ) : ℝ) * ((76293/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c95 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-844227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6439793/10000000) (δ := 223/25000000) (ψ := -393717/500000) 177 128
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t95 : ((-866210472183/10000000000000 : ℚ) : ℝ) ≤ stT177 95 := by
  have hc : ((-844277/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).2
  have h0 : (0:ℝ) ≤ ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-866210472183/10000000000000 : ℚ) : ℝ)
      = ((1025979/10000000 : ℚ) : ℝ) * ((-844277/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c96 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-279287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -231731/500000) (δ := 279/31250000) (ψ := -393717/500000) 177 129
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t96 : ((-285097208277/10000000000000 : ℚ) : ℝ) ≤ stT177 96 := by
  have hc : ((-279337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-285097208277/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-279337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c97 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((999807/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -49081/10000000) (δ := 279/31250000) (ψ := -393717/500000) 177 129
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t97 : ((507549635461/5000000000000 : ℚ) : ℝ) ≤ stT177 97 := by
  have hc : ((999757/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).1
  have hw2 : ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((507673/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((507549635461/5000000000000 : ℚ) : ℝ)
      = ((507673/5000000 : ℚ) : ℝ) * ((999757/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c98 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-223079/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 224471/500000) (δ := 71/8000000) (ψ := -393717/500000) 177 129
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t98 : ((-225394428737/10000000000000 : ℚ) : ℝ) ≤ stT177 98 := by
  have hc : ((-223129/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).2
  have h0 : (0:ℝ) ≤ ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-225394428737/10000000000000 : ℚ) : ℝ)
      = ((1010153/10000000 : ℚ) : ℝ) * ((-223129/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c99 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-449973/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3363053/5000000) (δ := 1787/200000000) (ψ := -393717/500000) 177 130
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t99 : ((-113066272481/1250000000000 : ℚ) : ℝ) ≤ stT177 99 := by
  have hc : ((-224999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113066272481/1250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-224999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c100 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((61253/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -35607/156250) (δ := 1807/200000000) (ψ := -393717/500000) 177 130
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t100 : ((956999043/15625000000 : ℚ) : ℝ) ≤ stT177 100 := by
  have hc : ((1914/3125 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((956999043/15625000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((1914/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c101 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((330111/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 531051/2500000) (δ := 1807/200000000) (ψ := -393717/500000) 177 130
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t101 : ((164223891591/2500000000000 : ℚ) : ℝ) ≤ stT177 101 := by
  have hc : ((165043/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164223891591/2500000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((165043/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c102 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-42677/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3241923/5000000) (δ := 1121/125000000) (ψ := -393717/500000) 177 130
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t102 : ((-21129510783/250000000000 : ℚ) : ℝ) ≤ stT177 102 := by
  have hc : ((-85359/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21129510783/250000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-85359/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c103 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-382057/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4907043/10000000) (δ := 8961/1000000000) (ψ := -393717/500000) 177 131
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t103 : ((-37650149031/1000000000000 : ℚ) : ℝ) ≤ stT177 103 := by
  have hc : ((-382107/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).2
  have h0 : (0:ℝ) ≤ ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-37650149031/1000000000000 : ℚ) : ℝ)
      = ((98533/1000000 : ℚ) : ℝ) * ((-382107/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c104 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((968251/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -157913/2500000) (δ := 8861/1000000000) (ψ := -393717/500000) 177 131
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t104 : ((47469926829/500000000000 : ℚ) : ℝ) ≤ stT177 104 := by
  have hc : ((968201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((47469926829/500000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((968201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c105 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((129293/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 900713/2500000) (δ := 4471/500000000) (ψ := -393717/500000) 177 131
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t105 : ((1261282437/100000000000 : ℚ) : ℝ) ≤ stT177 105 := by
  have hc : ((129243/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).1
  have hw2 : ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((9759/100000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1261282437/100000000000 : ℚ) : ℝ)
      = ((9759/100000 : ℚ) : ℝ) * ((129243/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c106 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-499871/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7797177/10000000) (δ := 4521/500000000) (ψ := -393717/500000) 177 131
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t106 : ((-30346374141/312500000000 : ℚ) : ℝ) ≤ stT177 106 := by
  have hc : ((-62487/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).2
  have h0 : (0:ℝ) ≤ ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-30346374141/312500000000 : ℚ) : ℝ)
      = ((485643/5000000 : ℚ) : ℝ) * ((-62487/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c107 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((68423/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -18779/50000) (δ := 8949/1000000000) (ψ := -393717/500000) 177 132
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t107 : ((4131165033/625000000000 : ℚ) : ℝ) ≤ stT177 107 := by
  have hc : ((68373/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4131165033/625000000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((68373/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c108 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((49481/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5633/156250) (δ := 8949/1000000000) (ψ := -393717/500000) 177 132
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t108 : ((380885493/4000000000 : ℚ) : ℝ) ≤ stT177 108 := by
  have hc : ((98957/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).1
  have hw2 : ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3849/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((380885493/4000000000 : ℚ) : ℝ)
      = ((3849/40000 : ℚ) : ℝ) * ((98957/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c109 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-203319/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4438857/10000000) (δ := 4477/500000000) (ψ := -393717/500000) 177 132
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t109 : ((-194792319163/10000000000000 : ℚ) : ℝ) ≤ stT177 109 := by
  have hc : ((-203369/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).2
  have h0 : (0:ℝ) ≤ ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-194792319163/10000000000000 : ℚ) : ℝ)
      = ((957827/10000000 : ℚ) : ℝ) * ((-203369/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c110 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-968813/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -289119/400000) (δ := 8947/1000000000) (ψ := -393717/500000) 177 133
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t110 : ((-923775022569/10000000000000 : ℚ) : ℝ) ≤ stT177 110 := by
  have hc : ((-968863/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).2
  have h0 : (0:ℝ) ≤ ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-923775022569/10000000000000 : ℚ) : ℝ)
      = ((953463/10000000 : ℚ) : ℝ) * ((-968863/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c111 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((138869/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1611697/5000000) (δ := 1107/125000000) (ψ := -393717/500000) 177 133
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t111 : ((32946188627/1250000000000 : ℚ) : ℝ) ≤ stT177 111 := by
  have hc : ((34711/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).1
  have hw2 : ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((949157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32946188627/1250000000000 : ℚ) : ℝ)
      = ((949157/10000000 : ℚ) : ℝ) * ((34711/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c112 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((955901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 745211/10000000) (δ := 9047/1000000000) (ψ := -393717/500000) 177 133
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t112 : ((903194124261/10000000000000 : ℚ) : ℝ) ≤ stT177 112 := by
  have hc : ((955851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((903194124261/10000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((955851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c113 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-296133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2339297/5000000) (δ := 1107/125000000) (ψ := -393717/500000) 177 133
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t113 : ((-278625567943/10000000000000 : ℚ) : ℝ) ≤ stT177 113 := by
  have hc : ((-296183/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).2
  have h0 : (0:ℝ) ≤ ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-278625567943/10000000000000 : ℚ) : ℝ)
      = ((940721/10000000 : ℚ) : ℝ) * ((-296183/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c114 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-479219/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7130679/10000000) (δ := 8939/1000000000) (ψ := -393717/500000) 177 134
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t114 : ((-56106652623/625000000000 : ℚ) : ℝ) ≤ stT177 114 := by
  have hc : ((-119811/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56106652623/625000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-119811/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c115 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((6533/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3266017/10000000) (δ := 9039/1000000000) (ψ := -393717/500000) 177 134
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t115 : ((3045441501/125000000000 : ℚ) : ℝ) ≤ stT177 115 := by
  have hc : ((26127/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3045441501/125000000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((26127/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c116 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((974557/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 141287/2500000) (δ := 9039/1000000000) (ψ := -393717/500000) 177 134
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t116 : ((226201590333/2500000000000 : ℚ) : ℝ) ≤ stT177 116 := by
  have hc : ((974507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((226201590333/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((974507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c117 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-17371/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 109087/250000) (δ := 277/31250000) (ψ := -393717/500000) 177 134
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t117 : ((-502004043/31250000000 : ℚ) : ℝ) ≤ stT177 117 := by
  have hc : ((-543/3125 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-502004043/31250000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-543/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c118 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-198787/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7578499/10000000) (δ := 1129/125000000) (ψ := -393717/500000) 177 135
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t118 : ((-7320301931/80000000000 : ℚ) : ℝ) ≤ stT177 118 := by
  have hc : ((-198797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7320301931/80000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-198797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c119 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((16529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -384433/1000000) (δ := 1129/125000000) (ψ := -393717/500000) 177 135
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t119 : ((945573987/312500000000 : ℚ) : ℝ) ≤ stT177 119 := by
  have hc : ((2063/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((945573987/312500000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((2063/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c120 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((499201/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -141357/10000000) (δ := 2233/250000000) (ψ := -393717/500000) 177 135
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t120 : ((5696034939/62500000000 : ℚ) : ℝ) ≤ stT177 120 := by
  have hc : ((62397/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).1
  have hw2 : ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((91287/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5696034939/62500000000 : ℚ) : ℝ)
      = ((91287/1000000 : ℚ) : ℝ) * ((62397/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c121 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((157789/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1765431/5000000) (δ := 2233/250000000) (ψ := -393717/500000) 177 135
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t121 : ((14339894751/1000000000000 : ℚ) : ℝ) ≤ stT177 121 := by
  have hc : ((157739/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).1
  have hw2 : ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((90909/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((14339894751/1000000000000 : ℚ) : ℝ)
      = ((90909/1000000 : ℚ) : ℝ) * ((157739/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c122 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-192623/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3586429/5000000) (δ := 1129/125000000) (ψ := -393717/500000) 177 135
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t122 : ((-87200913807/1000000000000 : ℚ) : ℝ) ≤ stT177 122 := by
  have hc : ((-192633/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).2
  have h0 : (0:ℝ) ≤ ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87200913807/1000000000000 : ℚ) : ℝ)
      = ((452679/5000000 : ℚ) : ℝ) * ((-192633/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c123 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-38789/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -984569/2000000) (δ := 361/40000000) (ψ := -393717/500000) 177 136
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t123 : ((-1748969299/50000000000 : ℚ) : ℝ) ≤ stT177 123 := by
  have hc : ((-19397/50000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).2
  have h0 : (0:ℝ) ≤ ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1748969299/50000000000 : ℚ) : ℝ)
      = ((90167/1000000 : ℚ) : ℝ) * ((-19397/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c124 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((53737/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -669917/5000000) (δ := 361/40000000) (ψ := -393717/500000) 177 136
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t124 : ((193017667323/2500000000000 : ℚ) : ℝ) ≤ stT177 124 := by
  have hc : ((429871/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).1
  have hw2 : ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((449013/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((193017667323/2500000000000 : ℚ) : ℝ)
      = ((449013/5000000 : ℚ) : ℝ) * ((429871/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c125 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((79087/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 442883/2000000) (δ := 4439/500000000) (ψ := -393717/500000) 177 136
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t125 : ((282927831921/5000000000000 : ℚ) : ℝ) ≤ stT177 125 := by
  have hc : ((316323/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((282927831921/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((316323/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c126 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-663391/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5740343/10000000) (δ := 361/40000000) (ψ := -393717/500000) 177 136
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t126 : ((-591040347111/10000000000000 : ℚ) : ℝ) ≤ stT177 126 := by
  have hc : ((-663441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).2
  have h0 : (0:ℝ) ≤ ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-591040347111/10000000000000 : ℚ) : ℝ)
      = ((890871/10000000 : ℚ) : ℝ) * ((-663441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c127 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-2658/3125 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6469613/10000000) (δ := 1777/200000000) (ψ := -393717/500000) 177 137
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t127 : ((-75479473777/1000000000000 : ℚ) : ℝ) ≤ stT177 127 := by
  have hc : ((-85061/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-75479473777/1000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-85061/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c128 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((90683/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2998997/10000000) (δ := 1777/200000000) (ψ := -393717/500000) 177 137
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t128 : ((160284227103/5000000000000 : ℚ) : ℝ) ≤ stT177 128 := by
  have hc : ((181341/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).1
  have hw2 : ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((160284227103/5000000000000 : ℚ) : ℝ)
      = ((883883/10000000 : ℚ) : ℝ) * ((181341/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c129 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((492113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 222313/5000000) (δ := 4509/500000000) (ψ := -393717/500000) 177 137
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t129 : ((1083147199/12500000000 : ℚ) : ℝ) ≤ stT177 129 := by
  have hc : ((61511/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1083147199/12500000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((61511/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c130 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((26149/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3861611/10000000) (δ := 4509/500000000) (ψ := -393717/500000) 177 137
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t130 : ((11445168371/5000000000000 : ℚ) : ℝ) ≤ stT177 130 := by
  have hc : ((26099/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11445168371/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((26099/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c131 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-121399/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1450489/2000000) (δ := 1797/200000000) (ψ := -393717/500000) 177 137
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t131 : ((-84857899161/1000000000000 : ℚ) : ℝ) ≤ stT177 131 := by
  have hc : ((-485621/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84857899161/1000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-485621/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c132 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-224389/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5090483/10000000) (δ := 2223/250000000) (ψ := -393717/500000) 177 138
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t132 : ((-97663738523/2500000000000 : ℚ) : ℝ) ≤ stT177 132 := by
  have hc : ((-112207/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97663738523/2500000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-112207/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c133 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((47789/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1750847/10000000) (δ := 2223/250000000) (ψ := -393717/500000) 177 138
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t133 : ((331484498283/5000000000000 : ℚ) : ℝ) ≤ stT177 133 := by
  have hc : ((382287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((331484498283/5000000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((382287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c134 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((810667/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 781883/5000000) (δ := 4473/250000000) (ψ := -393717/500000) 177 138
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t134 : ((175066521639/2500000000000 : ℚ) : ℝ) ≤ stT177 134 := by
  have hc : ((810617/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).1
  have hw2 : ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((215967/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((175066521639/2500000000000 : ℚ) : ℝ)
      = ((215967/2500000 : ℚ) : ℝ) * ((810617/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c135 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-45283/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4853731/10000000) (δ := 2223/250000000) (ψ := -393717/500000) 177 138
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t135 : ((-155915127091/5000000000000 : ℚ) : ℝ) ≤ stT177 135 := by
  have hc : ((-181157/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-155915127091/5000000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-181157/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c136 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-15537/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3794269/5000000) (δ := 8899/1000000000) (ψ := -393717/500000) 177 139
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t136 : ((-426353237037/5000000000000 : ℚ) : ℝ) ≤ stT177 136 := by
  have hc : ((-497209/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).2
  have h0 : (0:ℝ) ≤ ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-426353237037/5000000000000 : ℚ) : ℝ)
      = ((857493/10000000 : ℚ) : ℝ) * ((-497209/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c137 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-20889/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4346739/10000000) (δ := 1113/125000000) (ψ := -393717/500000) 177 139
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t137 : ((-35704047999/2500000000000 : ℚ) : ℝ) ≤ stT177 137 := by
  have hc : ((-83581/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).2
  have h0 : (0:ℝ) ≤ ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35704047999/2500000000000 : ℚ) : ℝ)
      = ((427179/5000000 : ℚ) : ℝ) * ((-83581/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c138 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((35993/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1128569/10000000) (δ := 8899/1000000000) (ψ := -393717/500000) 177 139
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t138 : ((3829694337/50000000000 : ℚ) : ℝ) ≤ stT177 138 := by
  have hc : ((35991/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).1
  have hw2 : ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((106407/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3829694337/50000000000 : ℚ) : ℝ)
      = ((106407/1250000 : ℚ) : ℝ) * ((35991/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c139 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((338703/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1033207/5000000) (δ := 8999/1000000000) (ψ := -393717/500000) 177 139
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t139 : ((35907826933/625000000000 : ℚ) : ℝ) ≤ stT177 139 := by
  have hc : ((169339/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).1
  have hw2 : ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((212047/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35907826933/625000000000 : ℚ) : ℝ)
      = ((212047/2500000 : ℚ) : ℝ) * ((169339/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c140 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-500861/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 209539/400000) (δ := 8899/1000000000) (ψ := -393717/500000) 177 139
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t140 : ((-84669487241/2000000000000 : ℚ) : ℝ) ≤ stT177 140 := by
  have hc : ((-500911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).2
  have h0 : (0:ℝ) ≤ ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-84669487241/2000000000000 : ℚ) : ℝ)
      = ((169031/2000000 : ℚ) : ℝ) * ((-500911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c141 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-977279/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7320039/10000000) (δ := 139/15625000) (ψ := -393717/500000) 177 140
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t141 : ((-102882446501/1250000000000 : ℚ) : ℝ) ≤ stT177 141 := by
  have hc : ((-977329/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).2
  have h0 : (0:ℝ) ≤ ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102882446501/1250000000000 : ℚ) : ℝ)
      = ((105269/1250000 : ℚ) : ℝ) * ((-977329/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c142 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-849/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4192803/10000000) (δ := 139/15625000) (ψ := -393717/500000) 177 140
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t142 : ((-1782002977/200000000000 : ℚ) : ℝ) ≤ stT177 142 := by
  have hc : ((-4247/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1782002977/200000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-4247/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c143 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((226717/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -217503/2000000) (δ := 139/15625000) (ψ := -393717/500000) 177 140
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t143 : ((189579824489/2500000000000 : ℚ) : ℝ) ≤ stT177 143 := by
  have hc : ((453409/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).1
  have hw2 : ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((418121/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((189579824489/2500000000000 : ℚ) : ℝ)
      = ((418121/5000000 : ℚ) : ℝ) * ((453409/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c144 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((174457/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1996091/10000000) (δ := 9007/1000000000) (ψ := -393717/500000) 177 140
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t144 : ((290740717037/5000000000000 : ℚ) : ℝ) ≤ stT177 144 := by
  have hc : ((348889/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((290740717037/5000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((348889/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c145 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-437277/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1264603/2500000) (δ := 8907/1000000000) (ψ := -393717/500000) 177 140
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t145 : ((-72636078757/2000000000000 : ℚ) : ℝ) ≤ stT177 145 := by
  have hc : ((-437327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).2
  have h0 : (0:ℝ) ≤ ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72636078757/2000000000000 : ℚ) : ℝ)
      = ((166091/2000000 : ℚ) : ℝ) * ((-437327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c146 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-39807/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7608293/10000000) (δ := 4457/500000000) (ψ := -393717/500000) 177 141
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t146 : ((-16473083627/200000000000 : ℚ) : ℝ) ≤ stT177 146 := by
  have hc : ((-39809/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16473083627/200000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-39809/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c147 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-261269/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -573479/1250000) (δ := 4507/500000000) (ψ := -393717/500000) 177 141
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t147 : ((-215532514053/10000000000000 : ℚ) : ℝ) ≤ stT177 147 := by
  have hc : ((-261319/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-215532514053/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-261319/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c148 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((804997/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -317563/2000000) (δ := 4457/500000000) (ψ := -393717/500000) 177 141
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t148 : ((330830802159/5000000000000 : ℚ) : ℝ) ≤ stT177 148 := by
  have hc : ((804947/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((330830802159/5000000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((804947/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c149 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((169789/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174003/1250000) (δ := 8889/1000000000) (ψ := -393717/500000) 177 141
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t149 : ((139088219949/2000000000000 : ℚ) : ℝ) ≤ stT177 149 := by
  have hc : ((169779/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139088219949/2000000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((169779/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c150 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-42283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2175931/5000000) (δ := 8989/1000000000) (ψ := -393717/500000) 177 141
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t150 : ((-69068297727/5000000000000 : ℚ) : ℝ) ≤ stT177 150 := by
  have hc : ((-84591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-69068297727/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-84591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c151 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-974849/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3646049/5000000) (δ := 4457/500000000) (ψ := -393717/500000) 177 141
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t151 : ((-793362082311/10000000000000 : ℚ) : ℝ) ≤ stT177 151 := by
  have hc : ((-974899/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-793362082311/10000000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-974899/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c152 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-586901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -343441/625000) (δ := 4491/500000000) (ψ := -393717/500000) 177 142
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t152 : ((-119020162927/2500000000000 : ℚ) : ℝ) ≤ stT177 152 := by
  have hc : ((-586951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).2
  have h0 : (0:ℝ) ≤ ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-119020162927/2500000000000 : ℚ) : ℝ)
      = ((202777/2500000 : ℚ) : ℝ) * ((-586951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c153 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((508493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1296703/5000000) (δ := 8921/1000000000) (ψ := -393717/500000) 177 142
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t153 : ((102762940059/2500000000000 : ℚ) : ℝ) ≤ stT177 153 := by
  have hc : ((508443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102762940059/2500000000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((508443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c154 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((99331/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289349/10000000) (δ := 9021/1000000000) (ψ := -393717/500000) 177 142
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t154 : ((20009768993/250000000000 : ℚ) : ℝ) ≤ stT177 154 := by
  have hc : ((49663/50000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).1
  have hw2 : ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((402911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20009768993/250000000000 : ℚ) : ℝ)
      = ((402911/5000000 : ℚ) : ℝ) * ((49663/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c155 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((30451/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 315343/1000000) (δ := 8921/1000000000) (ψ := -393717/500000) 177 142
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t155 : ((12227402837/500000000000 : ℚ) : ℝ) ≤ stT177 155 := by
  have hc : ((15223/50000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).1
  have hw2 : ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((803219/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12227402837/500000000000 : ℚ) : ℝ)
      = ((803219/10000000 : ℚ) : ℝ) * ((15223/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c156 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-737151/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5999103/10000000) (δ := 4441/500000000) (ψ := -393717/500000) 177 142
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t156 : ((-590233345841/10000000000000 : ℚ) : ℝ) ≤ stT177 156 := by
  have hc : ((-737201/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).2
  have h0 : (0:ℝ) ≤ ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-590233345841/10000000000000 : ℚ) : ℝ)
      = ((800641/10000000 : ℚ) : ℝ) * ((-737201/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c157 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-115659/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3440687/5000000) (δ := 359/40000000) (ψ := -393717/500000) 177 143
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t157 : ((-369243729507/5000000000000 : ℚ) : ℝ) ≤ stT177 157 := by
  have hc : ((-462661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).2
  have h0 : (0:ℝ) ≤ ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-369243729507/5000000000000 : ℚ) : ℝ)
      = ((798087/10000000 : ℚ) : ℝ) * ((-462661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c158 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-7239/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4071853/10000000) (δ := 359/40000000) (ψ := -393717/500000) 177 143
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t158 : ((-11528033199/2500000000000 : ℚ) : ℝ) ≤ stT177 158 := by
  have hc : ((-28981/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).2
  have h0 : (0:ℝ) ≤ ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11528033199/2500000000000 : ℚ) : ℝ)
      = ((397779/5000000 : ℚ) : ℝ) * ((-28981/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c159 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((10897/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -40001/312500) (δ := 359/40000000) (ψ := -393717/500000) 177 143
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t159 : ((69131048721/1000000000000 : ℚ) : ℝ) ≤ stT177 159 := by
  have hc : ((87171/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).1
  have hw2 : ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((793051/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((69131048721/1000000000000 : ℚ) : ℝ)
      = ((793051/10000000 : ℚ) : ℝ) * ((87171/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c160 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((826629/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 747133/5000000) (δ := 359/40000000) (ψ := -393717/500000) 177 143
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t160 : ((653467733451/10000000000000 : ℚ) : ℝ) ≤ stT177 160 := by
  have hc : ((826579/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).1
  have hw2 : ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((653467733451/10000000000000 : ℚ) : ℝ)
      = ((790569/10000000 : ℚ) : ℝ) * ((826579/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c161 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-25869/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4251263/10000000) (δ := 2257/250000000) (ψ := -393717/500000) 177 143
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t161 : ((-20395524569/2000000000000 : ℚ) : ℝ) ≤ stT177 161 := by
  have hc : ((-25879/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).2
  have h0 : (0:ℝ) ≤ ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-20395524569/2000000000000 : ℚ) : ℝ)
      = ((788111/10000000 : ℚ) : ℝ) * ((-25879/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c162 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-11763/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6991223/10000000) (δ := 2257/250000000) (ψ := -393717/500000) 177 143
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t162 : ((-2957563543/40000000000 : ℚ) : ℝ) ≤ stT177 162 := by
  have hc : ((-94109/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).2
  have h0 : (0:ℝ) ≤ ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2957563543/40000000000 : ℚ) : ℝ)
      = ((31427/400000 : ℚ) : ℝ) * ((-94109/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c163 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-735673/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -149841/250000) (δ := 2217/250000000) (ψ := -393717/500000) 177 144
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t163 : ((-576263132703/10000000000000 : ℚ) : ℝ) ≤ stT177 163 := by
  have hc : ((-735723/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-576263132703/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-735723/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c164 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((63281/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3287221/10000000) (δ := 1807/200000000) (ψ := -393717/500000) 177 144
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t164 : ((24702173529/1250000000000 : ℚ) : ℝ) ≤ stT177 164 := by
  have hc : ((126537/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).1
  have hw2 : ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((195217/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24702173529/1250000000000 : ℚ) : ℝ)
      = ((195217/2500000 : ℚ) : ℝ) * ((126537/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c165 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((485799/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -37329/625000) (δ := 2217/250000000) (ψ := -393717/500000) 177 144
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t165 : ((94543521863/1250000000000 : ℚ) : ℝ) ≤ stT177 165 := by
  have hc : ((242887/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((94543521863/1250000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((242887/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c166 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((337223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1038227/5000000) (δ := 1787/200000000) (ψ := -393717/500000) 177 144
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t166 : ((2617162277/50000000000 : ℚ) : ℝ) ≤ stT177 166 := by
  have hc : ((168599/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2617162277/50000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((168599/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c167 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-63457/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4734153/10000000) (δ := 2217/250000000) (ψ := -393717/500000) 177 144
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t167 : ((-767379497/31250000000 : ℚ) : ℝ) ≤ stT177 167 := by
  have hc : ((-63467/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).2
  have h0 : (0:ℝ) ≤ ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-767379497/31250000000 : ℚ) : ℝ)
      = ((12091/156250 : ℚ) : ℝ) * ((-63467/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c168 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-245443/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3687961/5000000) (δ := 1121/125000000) (ψ := -393717/500000) 177 144
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t168 : ((-378746181987/5000000000000 : ℚ) : ℝ) ≤ stT177 168 := by
  have hc : ((-490911/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-378746181987/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-490911/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c169 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-81627/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1426473/2500000) (δ := 443/50000000) (ψ := -393717/500000) 177 145
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t169 : ((-251179306123/5000000000000 : ℚ) : ℝ) ≤ stT177 169 := by
  have hc : ((-326533/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-251179306123/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-326533/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c170 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((326583/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -123811/400000) (δ := 7/781250) (ψ := -393717/500000) 177 145
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t170 : ((62609763953/2500000000000 : ℚ) : ℝ) ≤ stT177 170 := by
  have hc : ((326533/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((62609763953/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((326533/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c171 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((980069/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3906/78125) (δ := 443/50000000) (ψ := -393717/500000) 177 145
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t171 : ((749439149661/10000000000000 : ℚ) : ℝ) ≤ stT177 171 := by
  have hc : ((980019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((749439149661/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((980019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c172 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((336669/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 416041/2000000) (δ := 7/781250) (ψ := -393717/500000) 177 145
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t172 : ((16043022303/312500000000 : ℚ) : ℝ) ≤ stT177 172 := by
  have hc : ((84161/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).1
  have hw2 : ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((190623/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((16043022303/312500000000 : ℚ) : ℝ)
      = ((190623/2500000 : ℚ) : ℝ) * ((84161/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c173 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-283433/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2322711/5000000) (δ := 443/50000000) (ψ := -393717/500000) 177 145
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t173 : ((-107764078069/5000000000000 : ℚ) : ℝ) ≤ stT177 173 := by
  have hc : ((-283483/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107764078069/5000000000000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-283483/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c174 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-19311/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7195859/10000000) (δ := 7/781250) (ψ := -393717/500000) 177 145
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t174 : ((-915025493/12500000000 : ℚ) : ℝ) ≤ stT177 174 := by
  have hc : ((-1207/1250 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-915025493/12500000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-1207/1250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c175 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-730949/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5976269/10000000) (δ := 179/20000000) (ψ := -393717/500000) 177 146
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t175 : ((-552583343071/10000000000000 : ℚ) : ℝ) ≤ stT177 175 := by
  have hc : ((-730999/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).2
  have h0 : (0:ℝ) ≤ ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-552583343071/10000000000000 : ℚ) : ℝ)
      = ((755929/10000000 : ℚ) : ℝ) * ((-730999/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c176 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((93857/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -431863/1250000) (δ := 179/20000000) (ψ := -393717/500000) 177 146
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t176 : ((4420531081/312500000000 : ℚ) : ℝ) ≤ stT177 176 := by
  have hc : ((11729/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4420531081/312500000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((11729/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c177 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((29031/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -236947/2500000) (δ := 8953/1000000000) (ψ := -393717/500000) 177 146
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t177 : ((174558884633/2500000000000 : ℚ) : ℝ) ≤ stT177 177 := by
  have hc : ((464471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).1
  have hw2 : ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((375823/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174558884633/2500000000000 : ℚ) : ℝ)
      = ((375823/5000000 : ℚ) : ℝ) * ((464471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c178 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((163/200 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1545169/10000000) (δ := 179/20000000) (ψ := -393717/500000) 177 146
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t178 : ((12216605769/200000000000 : ℚ) : ℝ) ≤ stT177 178 := by
  have hc : ((16299/20000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).1
  have hw2 : ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((749531/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((12216605769/200000000000 : ℚ) : ℝ)
      = ((749531/10000000 : ℚ) : ℝ) * ((16299/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c179 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-38869/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4024187/10000000) (δ := 181/20000000) (ψ := -393717/500000) 177 146
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t179 : ((-7272365421/2500000000000 : ℚ) : ℝ) ≤ stT177 179 := by
  have hc : ((-38919/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7272365421/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-38919/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c180 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-427343/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3244677/5000000) (δ := 8853/1000000000) (ψ := -393717/500000) 177 146
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t180 : ((-9954415719/156250000000 : ℚ) : ℝ) ≤ stT177 180 := by
  have hc : ((-53421/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).2
  have h0 : (0:ℝ) ≤ ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9954415719/156250000000 : ℚ) : ℝ)
      = ((186339/2500000 : ℚ) : ℝ) * ((-53421/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c181 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-906969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6767071/10000000) (δ := 4473/500000000) (ψ := -393717/500000) 177 147
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t181 : ((-134836537521/2000000000000 : ℚ) : ℝ) ≤ stT177 181 := by
  have hc : ((-907019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).2
  have h0 : (0:ℝ) ≤ ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-134836537521/2000000000000 : ℚ) : ℝ)
      = ((148659/2000000 : ℚ) : ℝ) * ((-907019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c182 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-8007/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4329073/10000000) (δ := 4473/500000000) (ψ := -393717/500000) 177 147
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t182 : ((-9499267/800000000 : ℚ) : ℝ) ≤ stT177 182 := by
  have hc : ((-16019/100000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9499267/800000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-16019/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c183 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((90453/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -952197/5000000) (δ := 8857/1000000000) (ψ := -393717/500000) 177 147
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t183 : ((267440547927/5000000000000 : ℚ) : ℝ) ≤ stT177 183 := by
  have hc : ((361787/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).1
  have hw2 : ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((739221/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267440547927/5000000000000 : ℚ) : ℝ)
      = ((739221/10000000 : ℚ) : ℝ) * ((361787/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c184 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((489751/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 253527/5000000) (δ := 8857/1000000000) (ψ := -393717/500000) 177 147
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t184 : ((180515207367/2500000000000 : ℚ) : ℝ) ≤ stT177 184 := by
  have hc : ((244863/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).1
  have hw2 : ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((737209/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((180515207367/2500000000000 : ℚ) : ℝ)
      = ((737209/10000000 : ℚ) : ℝ) * ((244863/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c185 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((397341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 363181/1250000) (δ := 4473/500000000) (ψ := -393717/500000) 177 147
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t185 : ((146046952637/5000000000000 : ℚ) : ℝ) ≤ stT177 185 := by
  have hc : ((397291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((146046952637/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((397291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c186 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-129723/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5290877/10000000) (δ := 4473/500000000) (ψ := -393717/500000) 177 147
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t186 : ((-47563369539/1250000000000 : ℚ) : ℝ) ≤ stT177 186 := by
  have hc : ((-259471/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).2
  have h0 : (0:ℝ) ≤ ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-47563369539/1250000000000 : ℚ) : ℝ)
      = ((183309/2500000 : ℚ) : ℝ) * ((-259471/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c187 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-997101/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3831781/5000000) (δ := 4473/500000000) (ψ := -393717/500000) 177 147
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t187 : ((-729189603223/10000000000000 : ℚ) : ℝ) ≤ stT177 187 := by
  have hc : ((-997151/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-729189603223/10000000000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-997151/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c188 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-323243/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -88819/156250) (δ := 8939/1000000000) (ψ := -393717/500000) 177 148
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t188 : ((-2357674341/50000000000 : ℚ) : ℝ) ≤ stT177 188 := by
  have hc : ((-80817/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2357674341/50000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-80817/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c189 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((233847/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3336909/10000000) (δ := 277/31250000) (ψ := -393717/500000) 177 148
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t189 : ((5314439607/312500000000 : ℚ) : ℝ) ≤ stT177 189 := by
  have hc : ((233797/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).1
  have hw2 : ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((22731/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5314439607/312500000000 : ℚ) : ℝ)
      = ((22731/312500 : ℚ) : ℝ) * ((233797/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c190 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((36831/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1001837/10000000) (δ := 9039/1000000000) (ψ := -393717/500000) 177 148
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t190 : ((6679638901/100000000000 : ℚ) : ℝ) ≤ stT177 190 := by
  have hc : ((36829/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6679638901/100000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((36829/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c191 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((86361/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1321023/10000000) (δ := 277/31250000) (ψ := -393717/500000) 177 148
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t191 : ((7810619543/125000000000 : ℚ) : ℝ) ≤ stT177 191 := by
  have hc : ((21589/25000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7810619543/125000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((21589/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c192 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((29459/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1815857/5000000) (δ := 2241/250000000) (ψ := -393717/500000) 177 148
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t192 : ((42502312491/5000000000000 : ℚ) : ℝ) ≤ stT177 192 := by
  have hc : ((58893/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((42502312491/5000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((58893/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c193 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-718309/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5930413/10000000) (δ := 2241/250000000) (ψ := -393717/500000) 177 148
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t193 : ((-64635787743/1250000000000 : ℚ) : ℝ) ≤ stT177 193 := by
  have hc : ((-718359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-64635787743/1250000000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-718359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c194 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-989461/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7490711/10000000) (δ := 1129/125000000) (ψ := -393717/500000) 177 149
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t194 : ((-710428328049/10000000000000 : ℚ) : ℝ) ≤ stT177 194 := by
  have hc : ((-989511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-710428328049/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-989511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c195 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-98587/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5215641/10000000) (δ := 8871/1000000000) (ψ := -393717/500000) 177 149
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t195 : ((-14121358131/400000000000 : ℚ) : ℝ) ≤ stT177 195 := by
  have hc : ((-98597/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).2
  have h0 : (0:ℝ) ≤ ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-14121358131/400000000000 : ℚ) : ℝ)
      = ((143223/2000000 : ℚ) : ℝ) * ((-98597/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c196 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((95027/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2952209/10000000) (δ := 8971/1000000000) (ψ := -393717/500000) 177 149
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t196 : ((27146972853/1000000000000 : ℚ) : ℝ) ≤ stT177 196 := by
  have hc : ((190029/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((27146972853/1000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((190029/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c197 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((15016/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -700283/10000000) (δ := 1129/125000000) (ψ := -393717/500000) 177 149
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t197 : ((34233257289/500000000000 : ℚ) : ℝ) ≤ stT177 197 := by
  have hc : ((480487/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((34233257289/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((480487/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c198 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((816143/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 385057/2500000) (δ := 8971/1000000000) (ψ := -393717/500000) 177 149
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t198 : ((579971996217/10000000000000 : ℚ) : ℝ) ≤ stT177 198 := by
  have hc : ((816093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).1
  have hw2 : ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((710669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((579971996217/10000000000000 : ℚ) : ℝ)
      = ((710669/10000000 : ℚ) : ℝ) * ((816093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c199 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((62973/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1884727/5000000) (δ := 2233/250000000) (ψ := -393717/500000) 177 149
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t199 : ((44604919163/10000000000000 : ℚ) : ℝ) ≤ stT177 199 := by
  have hc : ((62923/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).1
  have hw2 : ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((708881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((44604919163/10000000000000 : ℚ) : ℝ)
      = ((708881/10000000 : ℚ) : ℝ) * ((62923/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c200 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-734003/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1197497/2000000) (δ := 1129/125000000) (ψ := -393717/500000) 177 149
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t200 : ((-519054014671/10000000000000 : ℚ) : ℝ) ≤ stT177 200 := by
  have hc : ((-734053/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-519054014671/10000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-734053/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c201 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-495369/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1502693/2000000) (δ := 357/40000000) (ψ := -393717/500000) 177 150
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t201 : ((-87356044081/1250000000000 : ℚ) : ℝ) ≤ stT177 201 := by
  have hc : ((-247697/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).2
  have h0 : (0:ℝ) ≤ ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-87356044081/1250000000000 : ℚ) : ℝ)
      = ((352673/5000000 : ℚ) : ℝ) * ((-247697/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c202 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-131989/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -531747/1000000) (δ := 4439/500000000) (ψ := -393717/500000) 177 150
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t202 : ((-92875991397/2500000000000 : ℚ) : ℝ) ≤ stT177 202 := by
  have hc : ((-264003/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).2
  have h0 : (0:ℝ) ≤ ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92875991397/2500000000000 : ℚ) : ℝ)
      = ((351799/5000000 : ℚ) : ℝ) * ((-264003/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c203 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((312561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -195767/625000) (δ := 4489/500000000) (ψ := -393717/500000) 177 150
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t203 : ((109669797741/5000000000000 : ℚ) : ℝ) ≤ stT177 203 := by
  have hc : ((312511/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((109669797741/5000000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((312511/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c204 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((927499/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -957827/10000000) (δ := 4489/500000000) (ψ := -393717/500000) 177 150
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t204 : ((32467207143/500000000000 : ℚ) : ℝ) ≤ stT177 204 := by
  have hc : ((927449/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).1
  have hw2 : ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((35007/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32467207143/500000000000 : ℚ) : ℝ)
      = ((35007/500000 : ℚ) : ℝ) * ((927449/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c205 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((221471/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 602999/5000000) (δ := 4489/500000000) (ψ := -393717/500000) 177 150
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t205 : ((30934652031/500000000000 : ℚ) : ℝ) ≤ stT177 205 := by
  have hc : ((442917/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).1
  have hw2 : ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((69843/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((30934652031/500000000000 : ℚ) : ℝ)
      = ((69843/1000000 : ℚ) : ℝ) * ((442917/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c206 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((225133/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3359291/10000000) (δ := 357/40000000) (ψ := -393717/500000) 177 150
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t206 : ((156822753839/10000000000000 : ℚ) : ℝ) ≤ stT177 206 := by
  have hc : ((225083/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((156822753839/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((225083/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c207 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-294597/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2751071/5000000) (δ := 4489/500000000) (ψ := -393717/500000) 177 150
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t207 : ((-102388363239/2500000000000 : ℚ) : ℝ) ≤ stT177 207 := by
  have hc : ((-147311/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).2
  have h0 : (0:ℝ) ≤ ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-102388363239/2500000000000 : ℚ) : ℝ)
      = ((695049/10000000 : ℚ) : ℝ) * ((-147311/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c208 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-199231/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3817341/5000000) (δ := 4439/500000000) (ψ := -393717/500000) 177 150
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t208 : ((-1079288497/15625000000 : ℚ) : ℝ) ≤ stT177 208 := by
  have hc : ((-199241/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).2
  have h0 : (0:ℝ) ≤ ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1079288497/15625000000 : ℚ) : ℝ)
      = ((5417/78125 : ℚ) : ℝ) * ((-199241/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c209 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-181001/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5950963/10000000) (δ := 8917/1000000000) (ψ := -393717/500000) 177 151
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t209 : ((-50083901261/1000000000000 : ℚ) : ℝ) ≤ stT177 209 := by
  have hc : ((-362027/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50083901261/1000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-362027/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c210 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((17639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1919389/5000000) (δ := 9017/1000000000) (ψ := -393717/500000) 177 151
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t210 : ((1215480491/500000000000 : ℚ) : ℝ) ≤ stT177 210 := by
  have hc : ((8807/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).1
  have hw2 : ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((138013/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1215480491/500000000000 : ℚ) : ℝ)
      = ((138013/2000000 : ℚ) : ℝ) * ((8807/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c211 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((30731/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1736637/10000000) (δ := 4443/500000000) (ψ := -393717/500000) 177 151
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t211 : ((5288676003/100000000000 : ℚ) : ℝ) ≤ stT177 211 := by
  have hc : ((30729/40000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).1
  have hw2 : ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((172107/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5288676003/100000000000 : ℚ) : ℝ)
      = ((172107/2500000 : ℚ) : ℝ) * ((30729/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c212 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((61869/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 355547/10000000) (δ := 8917/1000000000) (ψ := -393717/500000) 177 151
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t212 : ((169958426727/2500000000000 : ℚ) : ℝ) ≤ stT177 212 := by
  have hc : ((494927/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((169958426727/2500000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((494927/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c213 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((561033/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609477/2500000) (δ := 4443/500000000) (ψ := -393717/500000) 177 151
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t213 : ((96094704951/2500000000000 : ℚ) : ℝ) ≤ stT177 213 := by
  have hc : ((560983/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((96094704951/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((560983/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c214 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-231303/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2255267/5000000) (δ := 4493/500000000) (ψ := -393717/500000) 177 151
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t214 : ((-79074835929/5000000000000 : ℚ) : ℝ) ≤ stT177 214 := by
  have hc : ((-231353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).2
  have h0 : (0:ℝ) ≤ ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79074835929/5000000000000 : ℚ) : ℝ)
      = ((341793/5000000 : ℚ) : ℝ) * ((-231353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c215 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-435833/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6573469/10000000) (δ := 4493/500000000) (ψ := -393717/500000) 177 151
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t215 : ((-29725297671/500000000000 : ℚ) : ℝ) ≤ stT177 215 := by
  have hc : ((-217929/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29725297671/500000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-217929/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c216 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-476297/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3540559/5000000) (δ := 901/100000000) (ψ := -393717/500000) 177 152
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t216 : ((-81024039327/1250000000000 : ℚ) : ℝ) ≤ stT177 216 := by
  have hc : ((-238161/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-81024039327/1250000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-238161/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c217 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-8593/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2518627/5000000) (δ := 8993/1000000000) (ψ := -393717/500000) 177 152
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t217 : ((-583399393/20000000000 : ℚ) : ℝ) ≤ stT177 217 := by
  have hc : ((-4297/10000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-583399393/20000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-4297/10000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c218 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((90331/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -750693/2500000) (δ := 8893/1000000000) (ψ := -393717/500000) 177 152
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t218 : ((24468546109/1000000000000 : ℚ) : ℝ) ≤ stT177 218 := by
  have hc : ((180637/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((24468546109/1000000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((180637/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c219 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((231129/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -488791/5000000) (δ := 8993/1000000000) (ψ := -393717/500000) 177 152
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t219 : ((312347940721/5000000000000 : ℚ) : ℝ) ≤ stT177 219 := by
  have hc : ((462233/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((312347940721/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((462233/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c220 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((457489/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1038359/10000000) (δ := 891/100000000) (ψ := -393717/500000) 177 152
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t220 : ((38552721417/625000000000 : ℚ) : ℝ) ≤ stT177 220 := by
  have hc : ((57183/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38552721417/625000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((57183/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c221 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((172727/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 609037/2000000) (δ := 891/100000000) (ψ := -393717/500000) 177 152
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t221 : ((1815184371/78125000000 : ℚ) : ℝ) ≤ stT177 221 := by
  have hc : ((86351/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).1
  have hw2 : ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((21021/312500 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1815184371/78125000000 : ℚ) : ℝ)
      = ((21021/312500 : ℚ) : ℝ) * ((86351/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c222 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-431687/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 315181/625000) (δ := 8993/1000000000) (ψ := -393717/500000) 177 152
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t222 : ((-289763309709/10000000000000 : ℚ) : ℝ) ≤ stT177 222 := by
  have hc : ((-431737/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-289763309709/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-431737/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c223 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-94639/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1757917/2500000) (δ := 8993/1000000000) (ψ := -393717/500000) 177 152
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t223 : ((-316891773/5000000000 : ℚ) : ℝ) ≤ stT177 223 := by
  have hc : ((-23661/25000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-316891773/5000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-23661/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c224 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-178941/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3348209/5000000) (δ := 8903/1000000000) (ψ := -393717/500000) 177 153
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t224 : ((-59783413227/1000000000000 : ℚ) : ℝ) ≤ stT177 224 := by
  have hc : ((-178951/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).2
  have h0 : (0:ℝ) ≤ ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59783413227/1000000000000 : ℚ) : ℝ)
      = ((334077/5000000 : ℚ) : ℝ) * ((-178951/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c225 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-156971/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2362673/5000000) (δ := 8903/1000000000) (ψ := -393717/500000) 177 153
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t225 : ((-26166013083/1250000000000 : ℚ) : ℝ) ≤ stT177 225 := by
  have hc : ((-39249/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).2
  have h0 : (0:ℝ) ≤ ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-26166013083/1250000000000 : ℚ) : ℝ)
      = ((666667/10000000 : ℚ) : ℝ) * ((-39249/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c226 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((89787/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2763057/10000000) (δ := 179/10000000) (ψ := -393717/500000) 177 153
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t226 : ((5971876263/200000000000 : ℚ) : ℝ) ≤ stT177 226 := by
  have hc : ((89777/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5971876263/200000000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((89777/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c227 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((474023/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -404699/5000000) (δ := 8903/1000000000) (ψ := -393717/500000) 177 153
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t227 : ((157301687277/2500000000000 : ℚ) : ℝ) ≤ stT177 227 := by
  have hc : ((236999/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((157301687277/2500000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((236999/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c228 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((179717/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227131/2000000) (δ := 8903/1000000000) (ψ := -393717/500000) 177 153
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t228 : ((59506918031/1000000000000 : ℚ) : ℝ) ≤ stT177 228 := by
  have hc : ((179707/200000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).1
  have hw2 : ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((331133/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59506918031/1000000000000 : ℚ) : ℝ)
      = ((331133/5000000 : ℚ) : ℝ) * ((179707/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c229 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((335289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 768053/2500000) (δ := 8903/1000000000) (ψ := -393717/500000) 177 153
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t229 : ((110765982751/5000000000000 : ℚ) : ℝ) ≤ stT177 229 := by
  have hc : ((335239/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).1
  have hw2 : ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((330409/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((110765982751/5000000000000 : ℚ) : ℝ)
      = ((330409/5000000 : ℚ) : ℝ) * ((335239/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c230 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-208131/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5000317/10000000) (δ := 9003/1000000000) (ψ := -393717/500000) 177 153
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t230 : ((-34313527859/1250000000000 : ℚ) : ℝ) ≤ stT177 230 := by
  have hc : ((-52039/125000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34313527859/1250000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-52039/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c231 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-931031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6920059/10000000) (δ := 9003/1000000000) (ψ := -393717/500000) 177 153
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t231 : ((-19143956441/312500000000 : ℚ) : ℝ) ≤ stT177 231 := by
  have hc : ((-931081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).2
  have h0 : (0:ℝ) ≤ ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19143956441/312500000000 : ℚ) : ℝ)
      = ((20561/312500 : ℚ) : ℝ) * ((-931081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c232 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-57783/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6876481/10000000) (δ := 139/15625000) (ψ := -393717/500000) 177 154
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t232 : ((-303507984037/5000000000000 : ℚ) : ℝ) ≤ stT177 232 := by
  have hc : ((-462289/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).2
  have h0 : (0:ℝ) ≤ ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-303507984037/5000000000000 : ℚ) : ℝ)
      = ((656533/10000000 : ℚ) : ℝ) * ((-462289/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c233 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-50799/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1243311/2500000) (δ := 8907/1000000000) (ψ := -393717/500000) 177 154
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t233 : ((-66567273981/2500000000000 : ℚ) : ℝ) ≤ stT177 233 := by
  have hc : ((-203221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).2
  have h0 : (0:ℝ) ≤ ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-66567273981/2500000000000 : ℚ) : ℝ)
      = ((327561/5000000 : ℚ) : ℝ) * ((-203221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c234 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((6661/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3078149/10000000) (δ := 9007/1000000000) (ψ := -393717/500000) 177 154
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t234 : ((5442219/250000000 : ℚ) : ℝ) ≤ stT177 234 := by
  have hc : ((333/1000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).1
  have hw2 : ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((16343/250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5442219/250000000 : ℚ) : ℝ)
      = ((16343/250000 : ℚ) : ℝ) * ((333/1000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c235 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((55539/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -74447/625000) (δ := 9007/1000000000) (ψ := -393717/500000) 177 154
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t235 : ((36227606267/625000000000 : ℚ) : ℝ) ≤ stT177 235 := by
  have hc : ((444287/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).1
  have hw2 : ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((81541/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((36227606267/625000000000 : ℚ) : ℝ)
      = ((81541/1250000 : ℚ) : ℝ) * ((444287/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c236 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((962389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 137567/2000000) (δ := 2249/250000000) (ψ := -393717/500000) 177 154
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t236 : ((9787949969/156250000000 : ℚ) : ℝ) ≤ stT177 236 := by
  have hc : ((962339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).1
  have hw2 : ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((10171/156250 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((9787949969/156250000000 : ℚ) : ℝ)
      = ((10171/156250 : ℚ) : ℝ) * ((962339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c237 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((520343/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1279429/5000000) (δ := 139/15625000) (ψ := -393717/500000) 177 154
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t237 : ((337966203717/10000000000000 : ℚ) : ℝ) ≤ stT177 237 := by
  have hc : ((520293/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337966203717/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((520293/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c238 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-98357/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1105501/2500000) (δ := 2249/250000000) (ψ := -393717/500000) 177 154
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t238 : ((-7971450741/625000000000 : ℚ) : ℝ) ≤ stT177 238 := by
  have hc : ((-49191/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).2
  have h0 : (0:ℝ) ≤ ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-7971450741/625000000000 : ℚ) : ℝ)
      = ((162051/2500000 : ℚ) : ℝ) * ((-49191/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c239 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-403823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6277363/10000000) (δ := 9007/1000000000) (ψ := -393717/500000) 177 154
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t239 : ((-32653483407/625000000000 : ℚ) : ℝ) ≤ stT177 239 := by
  have hc : ((-50481/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).2
  have h0 : (0:ℝ) ≤ ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-32653483407/625000000000 : ℚ) : ℝ)
      = ((646847/10000000 : ℚ) : ℝ) * ((-50481/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c240 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-994131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3791493/5000000) (δ := 4457/500000000) (ψ := -393717/500000) 177 155
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t240 : ((-320870923569/5000000000000 : ℚ) : ℝ) ≤ stT177 240 := by
  have hc : ((-994181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).2
  have h0 : (0:ℝ) ≤ ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-320870923569/5000000000000 : ℚ) : ℝ)
      = ((322749/5000000 : ℚ) : ℝ) * ((-994181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c241 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-664207/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5743071/10000000) (δ := 4457/500000000) (ψ := -393717/500000) 177 155
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t241 : ((-427885796349/10000000000000 : ℚ) : ℝ) ≤ stT177 241 := by
  have hc : ((-664257/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-427885796349/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-664257/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c242 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((6489/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3910767/10000000) (δ := 4457/500000000) (ψ := -393717/500000) 177 155
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t242 : ((517392967/1250000000000 : ℚ) : ℝ) ≤ stT177 242 := by
  have hc : ((6439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).1
  have hw2 : ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80353/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517392967/1250000000000 : ℚ) : ℝ)
      = ((80353/1250000 : ℚ) : ℝ) * ((6439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c243 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((671613/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -208603/1000000) (δ := 8889/1000000000) (ψ := -393717/500000) 177 155
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t243 : ((861615329/20000000000 : ℚ) : ℝ) ≤ stT177 243 := by
  have hc : ((671563/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).1
  have hw2 : ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1283/20000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((861615329/20000000000 : ℚ) : ℝ)
      = ((1283/20000 : ℚ) : ℝ) * ((671563/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c244 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((994227/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -268771/10000000) (δ := 8889/1000000000) (ψ := -393717/500000) 177 155
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t244 : ((79557026071/1250000000000 : ℚ) : ℝ) ≤ stT177 244 := by
  have hc : ((994177/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79557026071/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((994177/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c245 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((407979/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 192629/1250000) (δ := 8857/500000000) (ψ := -393717/500000) 177 155
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t245 : ((32579002463/625000000000 : ℚ) : ℝ) ≤ stT177 245 := by
  have hc : ((203977/250000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((32579002463/625000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((203977/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c246 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((231287/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3343489/10000000) (δ := 8989/1000000000) (ψ := -393717/500000) 177 155
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t246 : ((18428895189/1250000000000 : ℚ) : ℝ) ≤ stT177 246 := by
  have hc : ((231237/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18428895189/1250000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((231237/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c247 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-465901/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5138623/10000000) (δ := 8989/1000000000) (ψ := -393717/500000) 177 155
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t247 : ((-59295526407/2000000000000 : ℚ) : ℝ) ≤ stT177 247 := by
  have hc : ((-465951/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59295526407/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-465951/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c248 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-14562/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 13853/20000) (δ := 8989/1000000000) (ψ := -393717/500000) 177 155
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t248 : ((-295916181009/5000000000000 : ℚ) : ℝ) ≤ stT177 248 := by
  have hc : ((-466009/500000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-295916181009/5000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-466009/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c249 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-942329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7000799/10000000) (δ := 8981/1000000000) (ψ := -393717/500000) 177 156
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t249 : ((-23888365271/400000000000 : ℚ) : ℝ) ≤ stT177 249 := by
  have hc : ((-942379/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23888365271/400000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-942379/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_c250 :
    |Real.cos (((177 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-248479/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2613607/5000000) (δ := 4511/500000000) (ψ := -393717/500000) 177 156
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st177_t250 : ((-2455747591/78125000000 : ℚ) : ℝ) ≤ stT177 250 := by
  have hc : ((-31063/62500 : ℚ) : ℝ)
      ≤ Real.cos (((177 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st177_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2455747591/78125000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-31063/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st177_p1 : ((44101/62500 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT177 (i+1) := by
  rw [Finset.sum_range_one]
  exact st177_t1

theorem st177_p2 : ((739076319031/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT177 (i+1))
      = (∑ i ∈ Finset.range 1, stT177 (i+1)) + stT177 2 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 1
    simpa using h
  have hprev := st177_p1
  have hstep := st177_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p3 : ((4060758439453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT177 (i+1))
      = (∑ i ∈ Finset.range 2, stT177 (i+1)) + stT177 3 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 2
    simpa using h
  have hprev := st177_p2
  have hstep := st177_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p4 : ((5155895939453/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT177 (i+1))
      = (∑ i ∈ Finset.range 3, stT177 (i+1)) + stT177 4 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 3
    simpa using h
  have hprev := st177_p3
  have hstep := st177_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p5 : ((2977071280253/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT177 (i+1))
      = (∑ i ∈ Finset.range 4, stT177 (i+1)) + stT177 5 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 4
    simpa using h
  have hprev := st177_p4
  have hstep := st177_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p6 : ((2650372780341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT177 (i+1))
      = (∑ i ∈ Finset.range 5, stT177 (i+1)) + stT177 6 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 5
    simpa using h
  have hprev := st177_p5
  have hstep := st177_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p7 : ((6185322627781/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT177 (i+1))
      = (∑ i ∈ Finset.range 6, stT177 (i+1)) + stT177 7 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 6
    simpa using h
  have hprev := st177_p6
  have hstep := st177_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p8 : ((5179070760507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT177 (i+1))
      = (∑ i ∈ Finset.range 7, stT177 (i+1)) + stT177 8 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 7
    simpa using h
  have hprev := st177_p7
  have hstep := st177_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p9 : ((8480230430391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT177 (i+1))
      = (∑ i ∈ Finset.range 8, stT177 (i+1)) + stT177 9 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 8
    simpa using h
  have hprev := st177_p8
  have hstep := st177_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p10 : ((2909065483329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT177 (i+1))
      = (∑ i ∈ Finset.range 9, stT177 (i+1)) + stT177 10 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 9
    simpa using h
  have hprev := st177_p9
  have hstep := st177_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p11 : ((1026815697093/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT177 (i+1))
      = (∑ i ∈ Finset.range 10, stT177 (i+1)) + stT177 11 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 10
    simpa using h
  have hprev := st177_p10
  have hstep := st177_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p12 : ((6146900847317/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT177 (i+1))
      = (∑ i ∈ Finset.range 11, stT177 (i+1)) + stT177 12 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 11
    simpa using h
  have hprev := st177_p11
  have hstep := st177_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p13 : ((1025953855717/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT177 (i+1))
      = (∑ i ∈ Finset.range 12, stT177 (i+1)) + stT177 13 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 12
    simpa using h
  have hprev := st177_p12
  have hstep := st177_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p14 : ((7638338613451/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT177 (i+1))
      = (∑ i ∈ Finset.range 13, stT177 (i+1)) + stT177 14 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 13
    simpa using h
  have hprev := st177_p13
  have hstep := st177_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p15 : ((543882222601/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT177 (i+1))
      = (∑ i ∈ Finset.range 14, stT177 (i+1)) + stT177 15 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 14
    simpa using h
  have hprev := st177_p14
  have hstep := st177_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p16 : ((574692972601/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT177 (i+1))
      = (∑ i ∈ Finset.range 15, stT177 (i+1)) + stT177 16 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 15
    simpa using h
  have hprev := st177_p15
  have hstep := st177_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p17 : ((799130566129/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT177 (i+1))
      = (∑ i ∈ Finset.range 16, stT177 (i+1)) + stT177 17 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 16
    simpa using h
  have hprev := st177_p16
  have hstep := st177_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p18 : ((5741982113229/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT177 (i+1))
      = (∑ i ∈ Finset.range 17, stT177 (i+1)) + stT177 18 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 17
    simpa using h
  have hprev := st177_p17
  have hstep := st177_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p19 : ((3904441107483/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT177 (i+1))
      = (∑ i ∈ Finset.range 18, stT177 (i+1)) + stT177 19 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 18
    simpa using h
  have hprev := st177_p18
  have hstep := st177_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p20 : ((111690534783/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT177 (i+1))
      = (∑ i ∈ Finset.range 19, stT177 (i+1)) + stT177 20 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 19
    simpa using h
  have hprev := st177_p19
  have hstep := st177_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p21 : ((3636458568477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT177 (i+1))
      = (∑ i ∈ Finset.range 20, stT177 (i+1)) + stT177 21 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 20
    simpa using h
  have hprev := st177_p20
  have hstep := st177_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p22 : ((7915011553137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT177 (i+1))
      = (∑ i ∈ Finset.range 21, stT177 (i+1)) + stT177 22 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 21
    simpa using h
  have hprev := st177_p21
  have hstep := st177_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p23 : ((1479504014503/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT177 (i+1))
      = (∑ i ∈ Finset.range 22, stT177 (i+1)) + stT177 23 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 22
    simpa using h
  have hprev := st177_p22
  have hstep := st177_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p24 : ((2371839664601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT177 (i+1))
      = (∑ i ∈ Finset.range 23, stT177 (i+1)) + stT177 24 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 23
    simpa using h
  have hprev := st177_p23
  have hstep := st177_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p25 : ((2695257664601/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT177 (i+1))
      = (∑ i ∈ Finset.range 24, stT177 (i+1)) + stT177 25 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 24
    simpa using h
  have hprev := st177_p24
  have hstep := st177_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p26 : ((1757033938597/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT177 (i+1))
      = (∑ i ∈ Finset.range 25, stT177 (i+1)) + stT177 26 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 25
    simpa using h
  have hprev := st177_p25
  have hstep := st177_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p27 : ((1114932412361/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT177 (i+1))
      = (∑ i ∈ Finset.range 26, stT177 (i+1)) + stT177 27 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 26
    simpa using h
  have hprev := st177_p26
  have hstep := st177_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p28 : ((5404116223839/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT177 (i+1))
      = (∑ i ∈ Finset.range 27, stT177 (i+1)) + stT177 28 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 27
    simpa using h
  have hprev := st177_p27
  have hstep := st177_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p29 : ((12655096622029/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT177 (i+1))
      = (∑ i ∈ Finset.range 28, stT177 (i+1)) + stT177 29 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 28
    simpa using h
  have hprev := st177_p28
  have hstep := st177_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p30 : ((7173060835431/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT177 (i+1))
      = (∑ i ∈ Finset.range 29, stT177 (i+1)) + stT177 30 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 29
    simpa using h
  have hprev := st177_p29
  have hstep := st177_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p31 : ((15509933481961/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT177 (i+1))
      = (∑ i ∈ Finset.range 30, stT177 (i+1)) + stT177 31 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 30
    simpa using h
  have hprev := st177_p30
  have hstep := st177_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p32 : ((15582892720313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT177 (i+1))
      = (∑ i ∈ Finset.range 31, stT177 (i+1)) + stT177 32 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 31
    simpa using h
  have hprev := st177_p31
  have hstep := st177_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p33 : ((716989409881/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT177 (i+1))
      = (∑ i ∈ Finset.range 32, stT177 (i+1)) + stT177 33 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 32
    simpa using h
  have hprev := st177_p32
  have hstep := st177_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p34 : ((3166860902381/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT177 (i+1))
      = (∑ i ∈ Finset.range 33, stT177 (i+1)) + stT177 34 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 33
    simpa using h
  have hprev := st177_p33
  have hstep := st177_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p35 : ((6170155673759/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT177 (i+1))
      = (∑ i ∈ Finset.range 34, stT177 (i+1)) + stT177 35 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 34
    simpa using h
  have hprev := st177_p34
  have hstep := st177_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p36 : ((6913625376371/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT177 (i+1))
      = (∑ i ∈ Finset.range 35, stT177 (i+1)) + stT177 36 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 35
    simpa using h
  have hprev := st177_p35
  have hstep := st177_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p37 : ((14763296989617/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT177 (i+1))
      = (∑ i ∈ Finset.range 36, stT177 (i+1)) + stT177 37 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 36
    simpa using h
  have hprev := st177_p36
  have hstep := st177_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p38 : ((3359252018033/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT177 (i+1))
      = (∑ i ∈ Finset.range 37, stT177 (i+1)) + stT177 38 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 37
    simpa using h
  have hprev := st177_p37
  have hstep := st177_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p39 : ((6335345275901/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT177 (i+1))
      = (∑ i ∈ Finset.range 38, stT177 (i+1)) + stT177 39 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 38
    simpa using h
  have hprev := st177_p38
  have hstep := st177_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p40 : ((55450704469/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT177 (i+1))
      = (∑ i ∈ Finset.range 39, stT177 (i+1)) + stT177 40 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 39
    simpa using h
  have hprev := st177_p39
  have hstep := st177_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p41 : ((7039939443399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT177 (i+1))
      = (∑ i ∈ Finset.range 40, stT177 (i+1)) + stT177 41 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 40
    simpa using h
  have hprev := st177_p40
  have hstep := st177_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p42 : ((6370781146823/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT177 (i+1))
      = (∑ i ∈ Finset.range 41, stT177 (i+1)) + stT177 42 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 41
    simpa using h
  have hprev := st177_p41
  have hstep := st177_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p43 : ((14078161321641/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT177 (i+1))
      = (∑ i ∈ Finset.range 42, stT177 (i+1)) + stT177 43 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 42
    simpa using h
  have hprev := st177_p42
  have hstep := st177_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p44 : ((34665448023/25000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT177 (i+1))
      = (∑ i ∈ Finset.range 43, stT177 (i+1)) + stT177 44 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 43
    simpa using h
  have hprev := st177_p43
  have hstep := st177_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p45 : ((806962626537/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT177 (i+1))
      = (∑ i ∈ Finset.range 44, stT177 (i+1)) + stT177 45 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 44
    simpa using h
  have hprev := st177_p44
  have hstep := st177_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p46 : ((14373862012083/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT177 (i+1))
      = (∑ i ∈ Finset.range 45, stT177 (i+1)) + stT177 46 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 45
    simpa using h
  have hprev := st177_p45
  have hstep := st177_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p47 : ((13121166098833/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT177 (i+1))
      = (∑ i ∈ Finset.range 46, stT177 (i+1)) + stT177 47 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 46
    simpa using h
  have hprev := st177_p46
  have hstep := st177_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p48 : ((6873139410479/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT177 (i+1))
      = (∑ i ∈ Finset.range 47, stT177 (i+1)) + stT177 48 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 47
    simpa using h
  have hprev := st177_p47
  have hstep := st177_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p49 : ((13831914509553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT177 (i+1))
      = (∑ i ∈ Finset.range 48, stT177 (i+1)) + stT177 49 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 48
    simpa using h
  have hprev := st177_p48
  have hstep := st177_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p50 : ((13160877037623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT177 (i+1))
      = (∑ i ∈ Finset.range 49, stT177 (i+1)) + stT177 50 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 49
    simpa using h
  have hprev := st177_p49
  have hstep := st177_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p51 : ((14219987217303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT177 (i+1))
      = (∑ i ∈ Finset.range 50, stT177 (i+1)) + stT177 51 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 50
    simpa using h
  have hprev := st177_p50
  have hstep := st177_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p52 : ((404760281451/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT177 (i+1))
      = (∑ i ∈ Finset.range 51, stT177 (i+1)) + stT177 52 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 51
    simpa using h
  have hprev := st177_p51
  have hstep := st177_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p53 : ((3575438266003/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT177 (i+1))
      = (∑ i ∈ Finset.range 52, stT177 (i+1)) + stT177 53 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 52
    simpa using h
  have hprev := st177_p52
  have hstep := st177_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p54 : ((1617643700079/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT177 (i+1))
      = (∑ i ∈ Finset.range 53, stT177 (i+1)) + stT177 54 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 53
    simpa using h
  have hprev := st177_p53
  have hstep := st177_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p55 : ((3571139881083/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT177 (i+1))
      = (∑ i ∈ Finset.range 54, stT177 (i+1)) + stT177 55 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 54
    simpa using h
  have hprev := st177_p54
  have hstep := st177_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p56 : ((12960013362239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT177 (i+1))
      = (∑ i ∈ Finset.range 55, stT177 (i+1)) + stT177 56 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 55
    simpa using h
  have hprev := st177_p55
  have hstep := st177_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p57 : ((14274247125939/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT177 (i+1))
      = (∑ i ∈ Finset.range 56, stT177 (i+1)) + stT177 57 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 56
    simpa using h
  have hprev := st177_p56
  have hstep := st177_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p58 : ((12963569278109/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT177 (i+1))
      = (∑ i ∈ Finset.range 57, stT177 (i+1)) + stT177 58 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 57
    simpa using h
  have hprev := st177_p57
  have hstep := st177_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p59 : ((14263442953937/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT177 (i+1))
      = (∑ i ∈ Finset.range 58, stT177 (i+1)) + stT177 59 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 58
    simpa using h
  have hprev := st177_p58
  have hstep := st177_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p60 : ((3250979634763/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT177 (i+1))
      = (∑ i ∈ Finset.range 59, stT177 (i+1)) + stT177 60 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 59
    simpa using h
  have hprev := st177_p59
  have hstep := st177_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p61 : ((3540922169283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT177 (i+1))
      = (∑ i ∈ Finset.range 60, stT177 (i+1)) + stT177 61 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 60
    simpa using h
  have hprev := st177_p60
  have hstep := st177_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p62 : ((6596494659237/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT177 (i+1))
      = (∑ i ∈ Finset.range 61, stT177 (i+1)) + stT177 62 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 61
    simpa using h
  have hprev := st177_p61
  have hstep := st177_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p63 : ((13862584572949/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT177 (i+1))
      = (∑ i ∈ Finset.range 62, stT177 (i+1)) + stT177 63 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 62
    simpa using h
  have hprev := st177_p62
  have hstep := st177_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p64 : ((6803262809051/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT177 (i+1))
      = (∑ i ∈ Finset.range 63, stT177 (i+1)) + stT177 64 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 63
    simpa using h
  have hprev := st177_p63
  have hstep := st177_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p65 : ((6685440912183/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT177 (i+1))
      = (∑ i ∈ Finset.range 64, stT177 (i+1)) + stT177 65 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 64
    simpa using h
  have hprev := st177_p64
  have hstep := st177_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p66 : ((7048171573359/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT177 (i+1))
      = (∑ i ∈ Finset.range 65, stT177 (i+1)) + stT177 66 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 65
    simpa using h
  have hprev := st177_p65
  have hstep := st177_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p67 : ((13001891346053/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT177 (i+1))
      = (∑ i ∈ Finset.range 66, stT177 (i+1)) + stT177 67 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 66
    simpa using h
  have hprev := st177_p66
  have hstep := st177_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p68 : ((14212416842603/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT177 (i+1))
      = (∑ i ∈ Finset.range 67, stT177 (i+1)) + stT177 68 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 67
    simpa using h
  have hprev := st177_p67
  have hstep := st177_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p69 : ((6615008066333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT177 (i+1))
      = (∑ i ∈ Finset.range 68, stT177 (i+1)) + stT177 69 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 68
    simpa using h
  have hprev := st177_p68
  have hstep := st177_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p70 : ((6825307835319/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT177 (i+1))
      = (∑ i ∈ Finset.range 69, stT177 (i+1)) + stT177 70 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 69
    simpa using h
  have hprev := st177_p69
  have hstep := st177_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p71 : ((13968555487319/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT177 (i+1))
      = (∑ i ∈ Finset.range 70, stT177 (i+1)) + stT177 71 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 70
    simpa using h
  have hprev := st177_p70
  have hstep := st177_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p72 : ((13018671279783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT177 (i+1))
      = (∑ i ∈ Finset.range 71, stT177 (i+1)) + stT177 72 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 71
    simpa using h
  have hprev := st177_p71
  have hstep := st177_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p73 : ((7093212138201/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT177 (i+1))
      = (∑ i ∈ Finset.range 72, stT177 (i+1)) + stT177 73 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 72
    simpa using h
  have hprev := st177_p72
  have hstep := st177_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p74 : ((13376516088209/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT177 (i+1))
      = (∑ i ∈ Finset.range 73, stT177 (i+1)) + stT177 74 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 73
    simpa using h
  have hprev := st177_p73
  have hstep := st177_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p75 : ((13382261875409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT177 (i+1))
      = (∑ i ∈ Finset.range 74, stT177 (i+1)) + stT177 75 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 74
    simpa using h
  have hprev := st177_p74
  have hstep := st177_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p76 : ((2839756593383/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT177 (i+1))
      = (∑ i ∈ Finset.range 75, stT177 (i+1)) + stT177 76 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 75
    simpa using h
  have hprev := st177_p75
  have hstep := st177_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p77 : ((104483991279/80000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT177 (i+1))
      = (∑ i ∈ Finset.range 76, stT177 (i+1)) + stT177 77 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 76
    simpa using h
  have hprev := st177_p76
  have hstep := st177_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p78 : ((13758146854317/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT177 (i+1))
      = (∑ i ∈ Finset.range 77, stT177 (i+1)) + stT177 78 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 77
    simpa using h
  have hprev := st177_p77
  have hstep := st177_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p79 : ((7003392727941/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT177 (i+1))
      = (∑ i ∈ Finset.range 78, stT177 (i+1)) + stT177 79 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 78
    simpa using h
  have hprev := st177_p78
  have hstep := st177_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p80 : ((3247942056669/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT177 (i+1))
      = (∑ i ∈ Finset.range 79, stT177 (i+1)) + stT177 80 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 79
    simpa using h
  have hprev := st177_p79
  have hstep := st177_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p81 : ((13961404796379/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT177 (i+1))
      = (∑ i ∈ Finset.range 80, stT177 (i+1)) + stT177 81 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 80
    simpa using h
  have hprev := st177_p80
  have hstep := st177_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p82 : ((13861032410823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT177 (i+1))
      = (∑ i ∈ Finset.range 81, stT177 (i+1)) + stT177 82 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 81
    simpa using h
  have hprev := st177_p81
  have hstep := st177_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p83 : ((12997670332743/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT177 (i+1))
      = (∑ i ∈ Finset.range 82, stT177 (i+1)) + stT177 83 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 82
    simpa using h
  have hprev := st177_p82
  have hstep := st177_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p84 : ((14020232397009/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT177 (i+1))
      = (∑ i ∈ Finset.range 83, stT177 (i+1)) + stT177 84 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 83
    simpa using h
  have hprev := st177_p83
  have hstep := st177_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p85 : ((13839084499479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT177 (i+1))
      = (∑ i ∈ Finset.range 84, stT177 (i+1)) + stT177 85 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 84
    simpa using h
  have hprev := st177_p84
  have hstep := st177_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p86 : ((12991902576247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT177 (i+1))
      = (∑ i ∈ Finset.range 85, stT177 (i+1)) + stT177 86 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 85
    simpa using h
  have hprev := st177_p85
  have hstep := st177_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p87 : ((13967177131959/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT177 (i+1))
      = (∑ i ∈ Finset.range 86, stT177 (i+1)) + stT177 87 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 86
    simpa using h
  have hprev := st177_p86
  have hstep := st177_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p88 : ((13941636742123/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT177 (i+1))
      = (∑ i ∈ Finset.range 87, stT177 (i+1)) + stT177 88 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 87
    simpa using h
  have hprev := st177_p87
  have hstep := st177_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p89 : ((12988557560389/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT177 (i+1))
      = (∑ i ∈ Finset.range 88, stT177 (i+1)) + stT177 89 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 88
    simpa using h
  have hprev := st177_p88
  have hstep := st177_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p90 : ((13787343207529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT177 (i+1))
      = (∑ i ∈ Finset.range 89, stT177 (i+1)) + stT177 90 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 89
    simpa using h
  have hprev := st177_p89
  have hstep := st177_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p91 : ((14122776266701/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT177 (i+1))
      = (∑ i ∈ Finset.range 90, stT177 (i+1)) + stT177 91 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 90
    simpa using h
  have hprev := st177_p90
  have hstep := st177_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p92 : ((3270224665723/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT177 (i+1))
      = (∑ i ∈ Finset.range 91, stT177 (i+1)) + stT177 92 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 91
    simpa using h
  have hprev := st177_p91
  have hstep := st177_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p93 : ((3366515935583/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT177 (i+1))
      = (∑ i ∈ Finset.range 92, stT177 (i+1)) + stT177 93 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 92
    simpa using h
  have hprev := st177_p92
  have hstep := st177_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p94 : ((7126482882931/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT177 (i+1))
      = (∑ i ∈ Finset.range 93, stT177 (i+1)) + stT177 94 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 93
    simpa using h
  have hprev := st177_p93
  have hstep := st177_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p95 : ((13386755293679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT177 (i+1))
      = (∑ i ∈ Finset.range 94, stT177 (i+1)) + stT177 95 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 94
    simpa using h
  have hprev := st177_p94
  have hstep := st177_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p96 : ((6550829042701/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT177 (i+1))
      = (∑ i ∈ Finset.range 95, stT177 (i+1)) + stT177 96 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 95
    simpa using h
  have hprev := st177_p95
  have hstep := st177_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p97 : ((3529189339081/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT177 (i+1))
      = (∑ i ∈ Finset.range 96, stT177 (i+1)) + stT177 97 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 96
    simpa using h
  have hprev := st177_p96
  have hstep := st177_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p98 : ((13891362927587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT177 (i+1))
      = (∑ i ∈ Finset.range 97, stT177 (i+1)) + stT177 98 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 97
    simpa using h
  have hprev := st177_p97
  have hstep := st177_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p99 : ((12986832747739/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT177 (i+1))
      = (∑ i ∈ Finset.range 98, stT177 (i+1)) + stT177 99 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 98
    simpa using h
  have hprev := st177_p98
  have hstep := st177_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p100 : ((13599312135259/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT177 (i+1))
      = (∑ i ∈ Finset.range 99, stT177 (i+1)) + stT177 100 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 99
    simpa using h
  have hprev := st177_p99
  have hstep := st177_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p101 : ((14256207701623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT177 (i+1))
      = (∑ i ∈ Finset.range 100, stT177 (i+1)) + stT177 101 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 100
    simpa using h
  have hprev := st177_p100
  have hstep := st177_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p102 : ((13411027270303/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT177 (i+1))
      = (∑ i ∈ Finset.range 101, stT177 (i+1)) + stT177 102 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 101
    simpa using h
  have hprev := st177_p101
  have hstep := st177_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p103 : ((13034525779993/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT177 (i+1))
      = (∑ i ∈ Finset.range 102, stT177 (i+1)) + stT177 103 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 102
    simpa using h
  have hprev := st177_p102
  have hstep := st177_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p104 : ((13983924316573/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT177 (i+1))
      = (∑ i ∈ Finset.range 103, stT177 (i+1)) + stT177 104 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 103
    simpa using h
  have hprev := st177_p103
  have hstep := st177_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p105 : ((14110052560273/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT177 (i+1))
      = (∑ i ∈ Finset.range 104, stT177 (i+1)) + stT177 105 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 104
    simpa using h
  have hprev := st177_p104
  have hstep := st177_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p106 : ((13138968587761/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT177 (i+1))
      = (∑ i ∈ Finset.range 105, stT177 (i+1)) + stT177 106 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 105
    simpa using h
  have hprev := st177_p105
  have hstep := st177_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p107 : ((13205067228289/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT177 (i+1))
      = (∑ i ∈ Finset.range 106, stT177 (i+1)) + stT177 107 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 106
    simpa using h
  have hprev := st177_p106
  have hstep := st177_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p108 : ((14157280960789/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT177 (i+1))
      = (∑ i ∈ Finset.range 107, stT177 (i+1)) + stT177 108 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 107
    simpa using h
  have hprev := st177_p107
  have hstep := st177_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p109 : ((6981244320813/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT177 (i+1))
      = (∑ i ∈ Finset.range 108, stT177 (i+1)) + stT177 109 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 108
    simpa using h
  have hprev := st177_p108
  have hstep := st177_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p110 : ((13038713619057/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT177 (i+1))
      = (∑ i ∈ Finset.range 109, stT177 (i+1)) + stT177 110 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 109
    simpa using h
  have hprev := st177_p109
  have hstep := st177_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p111 : ((13302283128073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT177 (i+1))
      = (∑ i ∈ Finset.range 110, stT177 (i+1)) + stT177 111 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 110
    simpa using h
  have hprev := st177_p110
  have hstep := st177_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p112 : ((7102738626167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT177 (i+1))
      = (∑ i ∈ Finset.range 111, stT177 (i+1)) + stT177 112 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 111
    simpa using h
  have hprev := st177_p111
  have hstep := st177_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p113 : ((13926851684391/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT177 (i+1))
      = (∑ i ∈ Finset.range 112, stT177 (i+1)) + stT177 113 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 112
    simpa using h
  have hprev := st177_p112
  have hstep := st177_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p114 : ((13029145242423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT177 (i+1))
      = (∑ i ∈ Finset.range 113, stT177 (i+1)) + stT177 114 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 113
    simpa using h
  have hprev := st177_p113
  have hstep := st177_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p115 : ((13272780562503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT177 (i+1))
      = (∑ i ∈ Finset.range 114, stT177 (i+1)) + stT177 115 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 114
    simpa using h
  have hprev := st177_p114
  have hstep := st177_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p116 : ((2835517384767/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT177 (i+1))
      = (∑ i ∈ Finset.range 115, stT177 (i+1)) + stT177 116 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 115
    simpa using h
  have hprev := st177_p115
  have hstep := st177_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p117 : ((560677825203/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT177 (i+1))
      = (∑ i ∈ Finset.range 116, stT177 (i+1)) + stT177 117 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 116
    simpa using h
  have hprev := st177_p116
  have hstep := st177_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p118 : ((131019078887/100000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT177 (i+1))
      = (∑ i ∈ Finset.range 117, stT177 (i+1)) + stT177 118 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 117
    simpa using h
  have hprev := st177_p117
  have hstep := st177_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p119 : ((3283041564071/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT177 (i+1))
      = (∑ i ∈ Finset.range 118, stT177 (i+1)) + stT177 119 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 118
    simpa using h
  have hprev := st177_p118
  have hstep := st177_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p120 : ((3510882961631/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT177 (i+1))
      = (∑ i ∈ Finset.range 119, stT177 (i+1)) + stT177 120 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 119
    simpa using h
  have hprev := st177_p119
  have hstep := st177_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p121 : ((7093465397017/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT177 (i+1))
      = (∑ i ∈ Finset.range 120, stT177 (i+1)) + stT177 121 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 120
    simpa using h
  have hprev := st177_p120
  have hstep := st177_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p122 : ((3328730413991/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT177 (i+1))
      = (∑ i ∈ Finset.range 121, stT177 (i+1)) + stT177 122 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 121
    simpa using h
  have hprev := st177_p121
  have hstep := st177_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p123 : ((3241281949041/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT177 (i+1))
      = (∑ i ∈ Finset.range 122, stT177 (i+1)) + stT177 123 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 122
    simpa using h
  have hprev := st177_p122
  have hstep := st177_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p124 : ((858574904091/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT177 (i+1))
      = (∑ i ∈ Finset.range 123, stT177 (i+1)) + stT177 124 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 123
    simpa using h
  have hprev := st177_p123
  have hstep := st177_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p125 : ((7151527064649/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT177 (i+1))
      = (∑ i ∈ Finset.range 124, stT177 (i+1)) + stT177 125 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 124
    simpa using h
  have hprev := st177_p124
  have hstep := st177_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p126 : ((13712013782187/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT177 (i+1))
      = (∑ i ∈ Finset.range 125, stT177 (i+1)) + stT177 126 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 125
    simpa using h
  have hprev := st177_p125
  have hstep := st177_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p127 : ((12957219044417/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT177 (i+1))
      = (∑ i ∈ Finset.range 126, stT177 (i+1)) + stT177 127 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 126
    simpa using h
  have hprev := st177_p126
  have hstep := st177_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p128 : ((13277787498623/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT177 (i+1))
      = (∑ i ∈ Finset.range 127, stT177 (i+1)) + stT177 128 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 127
    simpa using h
  have hprev := st177_p127
  have hstep := st177_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p129 : ((14144305257823/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT177 (i+1))
      = (∑ i ∈ Finset.range 128, stT177 (i+1)) + stT177 129 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 128
    simpa using h
  have hprev := st177_p128
  have hstep := st177_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p130 : ((2833439118913/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT177 (i+1))
      = (∑ i ∈ Finset.range 129, stT177 (i+1)) + stT177 130 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 129
    simpa using h
  have hprev := st177_p129
  have hstep := st177_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p131 : ((2663723320591/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT177 (i+1))
      = (∑ i ∈ Finset.range 130, stT177 (i+1)) + stT177 131 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 130
    simpa using h
  have hprev := st177_p130
  have hstep := st177_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p132 : ((12927961648863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT177 (i+1))
      = (∑ i ∈ Finset.range 131, stT177 (i+1)) + stT177 132 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 131
    simpa using h
  have hprev := st177_p131
  have hstep := st177_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p133 : ((13590930645429/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT177 (i+1))
      = (∑ i ∈ Finset.range 132, stT177 (i+1)) + stT177 133 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 132
    simpa using h
  have hprev := st177_p132
  have hstep := st177_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p134 : ((2858239346397/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT177 (i+1))
      = (∑ i ∈ Finset.range 133, stT177 (i+1)) + stT177 134 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 133
    simpa using h
  have hprev := st177_p133
  have hstep := st177_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p135 : ((13979366477803/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT177 (i+1))
      = (∑ i ∈ Finset.range 134, stT177 (i+1)) + stT177 135 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 134
    simpa using h
  have hprev := st177_p134
  have hstep := st177_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p136 : ((13126660003729/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT177 (i+1))
      = (∑ i ∈ Finset.range 135, stT177 (i+1)) + stT177 136 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 135
    simpa using h
  have hprev := st177_p135
  have hstep := st177_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p137 : ((12983843811733/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT177 (i+1))
      = (∑ i ∈ Finset.range 136, stT177 (i+1)) + stT177 137 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 136
    simpa using h
  have hprev := st177_p136
  have hstep := st177_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p138 : ((13749782679133/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT177 (i+1))
      = (∑ i ∈ Finset.range 137, stT177 (i+1)) + stT177 138 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 137
    simpa using h
  have hprev := st177_p137
  have hstep := st177_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p139 : ((14324307910061/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT177 (i+1))
      = (∑ i ∈ Finset.range 138, stT177 (i+1)) + stT177 139 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 138
    simpa using h
  have hprev := st177_p138
  have hstep := st177_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p140 : ((54300626851/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT177 (i+1))
      = (∑ i ∈ Finset.range 139, stT177 (i+1)) + stT177 140 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 139
    simpa using h
  have hprev := st177_p139
  have hstep := st177_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p141 : ((1634737612731/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT177 (i+1))
      = (∑ i ∈ Finset.range 140, stT177 (i+1)) + stT177 141 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 140
    simpa using h
  have hprev := st177_p140
  have hstep := st177_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p142 : ((6494400376499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT177 (i+1))
      = (∑ i ∈ Finset.range 141, stT177 (i+1)) + stT177 142 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 141
    simpa using h
  have hprev := st177_p141
  have hstep := st177_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p143 : ((6873560025477/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT177 (i+1))
      = (∑ i ∈ Finset.range 142, stT177 (i+1)) + stT177 143 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 142
    simpa using h
  have hprev := st177_p142
  have hstep := st177_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p144 : ((3582150371257/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT177 (i+1))
      = (∑ i ∈ Finset.range 143, stT177 (i+1)) + stT177 144 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 143
    simpa using h
  have hprev := st177_p143
  have hstep := st177_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p145 : ((13965421091243/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT177 (i+1))
      = (∑ i ∈ Finset.range 144, stT177 (i+1)) + stT177 145 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 144
    simpa using h
  have hprev := st177_p144
  have hstep := st177_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p146 : ((13141766909893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT177 (i+1))
      = (∑ i ∈ Finset.range 145, stT177 (i+1)) + stT177 146 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 145
    simpa using h
  have hprev := st177_p145
  have hstep := st177_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p147 : ((40394482487/31250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT177 (i+1))
      = (∑ i ∈ Finset.range 146, stT177 (i+1)) + stT177 147 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 146
    simpa using h
  have hprev := st177_p146
  have hstep := st177_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p148 : ((6793948000079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT177 (i+1))
      = (∑ i ∈ Finset.range 147, stT177 (i+1)) + stT177 148 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 147
    simpa using h
  have hprev := st177_p147
  have hstep := st177_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p149 : ((14283337099903/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT177 (i+1))
      = (∑ i ∈ Finset.range 148, stT177 (i+1)) + stT177 149 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 148
    simpa using h
  have hprev := st177_p148
  have hstep := st177_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p150 : ((14145200504449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT177 (i+1))
      = (∑ i ∈ Finset.range 149, stT177 (i+1)) + stT177 150 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 149
    simpa using h
  have hprev := st177_p149
  have hstep := st177_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p151 : ((6675919211069/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT177 (i+1))
      = (∑ i ∈ Finset.range 150, stT177 (i+1)) + stT177 151 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 150
    simpa using h
  have hprev := st177_p150
  have hstep := st177_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p152 : ((1287575777043/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT177 (i+1))
      = (∑ i ∈ Finset.range 151, stT177 (i+1)) + stT177 152 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 151
    simpa using h
  have hprev := st177_p151
  have hstep := st177_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p153 : ((6643404765333/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT177 (i+1))
      = (∑ i ∈ Finset.range 152, stT177 (i+1)) + stT177 153 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 152
    simpa using h
  have hprev := st177_p152
  have hstep := st177_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p154 : ((7043600145193/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT177 (i+1))
      = (∑ i ∈ Finset.range 153, stT177 (i+1)) + stT177 154 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 153
    simpa using h
  have hprev := st177_p153
  have hstep := st177_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p155 : ((7165874173563/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT177 (i+1))
      = (∑ i ∈ Finset.range 154, stT177 (i+1)) + stT177 155 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 154
    simpa using h
  have hprev := st177_p154
  have hstep := st177_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p156 : ((2748303000257/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT177 (i+1))
      = (∑ i ∈ Finset.range 155, stT177 (i+1)) + stT177 156 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 155
    simpa using h
  have hprev := st177_p155
  have hstep := st177_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p157 : ((13003027542271/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT177 (i+1))
      = (∑ i ∈ Finset.range 156, stT177 (i+1)) + stT177 157 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 156
    simpa using h
  have hprev := st177_p156
  have hstep := st177_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p158 : ((518276616379/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT177 (i+1))
      = (∑ i ∈ Finset.range 157, stT177 (i+1)) + stT177 158 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 157
    simpa using h
  have hprev := st177_p157
  have hstep := st177_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p159 : ((2729645179337/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT177 (i+1))
      = (∑ i ∈ Finset.range 158, stT177 (i+1)) + stT177 159 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 158
    simpa using h
  have hprev := st177_p158
  have hstep := st177_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p160 : ((1787711703767/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT177 (i+1))
      = (∑ i ∈ Finset.range 159, stT177 (i+1)) + stT177 160 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 159
    simpa using h
  have hprev := st177_p159
  have hstep := st177_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p161 : ((14199716007291/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT177 (i+1))
      = (∑ i ∈ Finset.range 160, stT177 (i+1)) + stT177 161 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 160
    simpa using h
  have hprev := st177_p160
  have hstep := st177_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p162 : ((13460325121541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT177 (i+1))
      = (∑ i ∈ Finset.range 161, stT177 (i+1)) + stT177 162 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 161
    simpa using h
  have hprev := st177_p161
  have hstep := st177_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p163 : ((6442030994419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT177 (i+1))
      = (∑ i ∈ Finset.range 162, stT177 (i+1)) + stT177 163 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 162
    simpa using h
  have hprev := st177_p162
  have hstep := st177_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p164 : ((1308167937707/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT177 (i+1))
      = (∑ i ∈ Finset.range 163, stT177 (i+1)) + stT177 164 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 163
    simpa using h
  have hprev := st177_p163
  have hstep := st177_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p165 : ((6919013775987/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT177 (i+1))
      = (∑ i ∈ Finset.range 164, stT177 (i+1)) + stT177 165 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 164
    simpa using h
  have hprev := st177_p164
  have hstep := st177_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p166 : ((7180730003687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT177 (i+1))
      = (∑ i ∈ Finset.range 165, stT177 (i+1)) + stT177 166 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 165
    simpa using h
  have hprev := st177_p165
  have hstep := st177_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p167 : ((7057949284167/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT177 (i+1))
      = (∑ i ∈ Finset.range 166, stT177 (i+1)) + stT177 167 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 166
    simpa using h
  have hprev := st177_p166
  have hstep := st177_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p168 : ((333960155109/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT177 (i+1))
      = (∑ i ∈ Finset.range 167, stT177 (i+1)) + stT177 168 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 167
    simpa using h
  have hprev := st177_p167
  have hstep := st177_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p169 : ((6428023796057/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT177 (i+1))
      = (∑ i ∈ Finset.range 168, stT177 (i+1)) + stT177 169 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 168
    simpa using h
  have hprev := st177_p168
  have hstep := st177_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p170 : ((6553243323963/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT177 (i+1))
      = (∑ i ∈ Finset.range 169, stT177 (i+1)) + stT177 170 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 169
    simpa using h
  have hprev := st177_p169
  have hstep := st177_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p171 : ((13855925797587/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT177 (i+1))
      = (∑ i ∈ Finset.range 170, stT177 (i+1)) + stT177 171 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 170
    simpa using h
  have hprev := st177_p170
  have hstep := st177_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p172 : ((14369302511283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT177 (i+1))
      = (∑ i ∈ Finset.range 171, stT177 (i+1)) + stT177 172 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 171
    simpa using h
  have hprev := st177_p171
  have hstep := st177_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p173 : ((2830754871029/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT177 (i+1))
      = (∑ i ∈ Finset.range 172, stT177 (i+1)) + stT177 173 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 172
    simpa using h
  have hprev := st177_p172
  have hstep := st177_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p174 : ((2684350792149/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT177 (i+1))
      = (∑ i ∈ Finset.range 173, stT177 (i+1)) + stT177 174 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 173
    simpa using h
  have hprev := st177_p173
  have hstep := st177_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p175 : ((6434585308837/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT177 (i+1))
      = (∑ i ∈ Finset.range 174, stT177 (i+1)) + stT177 175 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 174
    simpa using h
  have hprev := st177_p174
  have hstep := st177_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p176 : ((6505313806133/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT177 (i+1))
      = (∑ i ∈ Finset.range 175, stT177 (i+1)) + stT177 176 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 175
    simpa using h
  have hprev := st177_p175
  have hstep := st177_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p177 : ((6854431575399/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT177 (i+1))
      = (∑ i ∈ Finset.range 176, stT177 (i+1)) + stT177 177 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 176
    simpa using h
  have hprev := st177_p176
  have hstep := st177_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p178 : ((894980839953/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT177 (i+1))
      = (∑ i ∈ Finset.range 177, stT177 (i+1)) + stT177 178 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 177
    simpa using h
  have hprev := st177_p177
  have hstep := st177_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p179 : ((3572650994391/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT177 (i+1))
      = (∑ i ∈ Finset.range 178, stT177 (i+1)) + stT177 179 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 178
    simpa using h
  have hprev := st177_p178
  have hstep := st177_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p180 : ((3413380342887/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT177 (i+1))
      = (∑ i ∈ Finset.range 179, stT177 (i+1)) + stT177 180 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 179
    simpa using h
  have hprev := st177_p179
  have hstep := st177_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p181 : ((12979338683943/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT177 (i+1))
      = (∑ i ∈ Finset.range 180, stT177 (i+1)) + stT177 181 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 180
    simpa using h
  have hprev := st177_p180
  have hstep := st177_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p182 : ((12860597846443/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT177 (i+1))
      = (∑ i ∈ Finset.range 181, stT177 (i+1)) + stT177 182 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 181
    simpa using h
  have hprev := st177_p181
  have hstep := st177_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p183 : ((13395478942297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT177 (i+1))
      = (∑ i ∈ Finset.range 182, stT177 (i+1)) + stT177 183 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 182
    simpa using h
  have hprev := st177_p182
  have hstep := st177_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p184 : ((2823507954353/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT177 (i+1))
      = (∑ i ∈ Finset.range 183, stT177 (i+1)) + stT177 184 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 183
    simpa using h
  have hprev := st177_p183
  have hstep := st177_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p185 : ((14409633677039/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT177 (i+1))
      = (∑ i ∈ Finset.range 184, stT177 (i+1)) + stT177 185 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 184
    simpa using h
  have hprev := st177_p184
  have hstep := st177_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p186 : ((14029126720727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT177 (i+1))
      = (∑ i ∈ Finset.range 185, stT177 (i+1)) + stT177 186 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 185
    simpa using h
  have hprev := st177_p185
  have hstep := st177_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p187 : ((207811517461/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT177 (i+1))
      = (∑ i ∈ Finset.range 186, stT177 (i+1)) + stT177 187 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 186
    simpa using h
  have hprev := st177_p186
  have hstep := st177_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p188 : ((1603550281163/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT177 (i+1))
      = (∑ i ∈ Finset.range 187, stT177 (i+1)) + stT177 188 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 187
    simpa using h
  have hprev := st177_p187
  have hstep := st177_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p189 : ((1624808039591/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT177 (i+1))
      = (∑ i ∈ Finset.range 188, stT177 (i+1)) + stT177 189 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 188
    simpa using h
  have hprev := st177_p188
  have hstep := st177_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p190 : ((3416607051707/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT177 (i+1))
      = (∑ i ∈ Finset.range 189, stT177 (i+1)) + stT177 190 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 189
    simpa using h
  have hprev := st177_p189
  have hstep := st177_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p191 : ((3572819442567/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT177 (i+1))
      = (∑ i ∈ Finset.range 190, stT177 (i+1)) + stT177 191 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 190
    simpa using h
  have hprev := st177_p190
  have hstep := st177_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p192 : ((57505129581/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT177 (i+1))
      = (∑ i ∈ Finset.range 191, stT177 (i+1)) + stT177 192 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 191
    simpa using h
  have hprev := st177_p191
  have hstep := st177_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p193 : ((6929598046653/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT177 (i+1))
      = (∑ i ∈ Finset.range 192, stT177 (i+1)) + stT177 193 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 192
    simpa using h
  have hprev := st177_p192
  have hstep := st177_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p194 : ((13148767765257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT177 (i+1))
      = (∑ i ∈ Finset.range 193, stT177 (i+1)) + stT177 194 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 193
    simpa using h
  have hprev := st177_p193
  have hstep := st177_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p195 : ((6397866905991/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT177 (i+1))
      = (∑ i ∈ Finset.range 194, stT177 (i+1)) + stT177 195 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 194
    simpa using h
  have hprev := st177_p194
  have hstep := st177_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p196 : ((408350110641/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT177 (i+1))
      = (∑ i ∈ Finset.range 195, stT177 (i+1)) + stT177 196 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 195
    simpa using h
  have hprev := st177_p195
  have hstep := st177_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p197 : ((3437967171573/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT177 (i+1))
      = (∑ i ∈ Finset.range 196, stT177 (i+1)) + stT177 197 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 196
    simpa using h
  have hprev := st177_p196
  have hstep := st177_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p198 : ((14331840682509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT177 (i+1))
      = (∑ i ∈ Finset.range 197, stT177 (i+1)) + stT177 198 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 197
    simpa using h
  have hprev := st177_p197
  have hstep := st177_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p199 : ((1797055700209/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT177 (i+1))
      = (∑ i ∈ Finset.range 198, stT177 (i+1)) + stT177 199 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 198
    simpa using h
  have hprev := st177_p198
  have hstep := st177_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p200 : ((13857391587001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT177 (i+1))
      = (∑ i ∈ Finset.range 199, stT177 (i+1)) + stT177 200 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 199
    simpa using h
  have hprev := st177_p199
  have hstep := st177_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p201 : ((13158543234353/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT177 (i+1))
      = (∑ i ∈ Finset.range 200, stT177 (i+1)) + stT177 201 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 200
    simpa using h
  have hprev := st177_p200
  have hstep := st177_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p202 : ((2557407853753/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT177 (i+1))
      = (∑ i ∈ Finset.range 201, stT177 (i+1)) + stT177 202 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 201
    simpa using h
  have hprev := st177_p201
  have hstep := st177_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p203 : ((13006378864247/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT177 (i+1))
      = (∑ i ∈ Finset.range 202, stT177 (i+1)) + stT177 203 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 202
    simpa using h
  have hprev := st177_p202
  have hstep := st177_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p204 : ((13655723007107/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT177 (i+1))
      = (∑ i ∈ Finset.range 203, stT177 (i+1)) + stT177 204 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 203
    simpa using h
  have hprev := st177_p203
  have hstep := st177_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p205 : ((14274416047727/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT177 (i+1))
      = (∑ i ∈ Finset.range 204, stT177 (i+1)) + stT177 205 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 204
    simpa using h
  have hprev := st177_p204
  have hstep := st177_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p206 : ((7215619400783/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT177 (i+1))
      = (∑ i ∈ Finset.range 205, stT177 (i+1)) + stT177 206 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 205
    simpa using h
  have hprev := st177_p205
  have hstep := st177_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p207 : ((1402168534861/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT177 (i+1))
      = (∑ i ∈ Finset.range 206, stT177 (i+1)) + stT177 207 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 206
    simpa using h
  have hprev := st177_p206
  have hstep := st177_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p208 : ((1333094071053/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT177 (i+1))
      = (∑ i ∈ Finset.range 207, stT177 (i+1)) + stT177 208 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 207
    simpa using h
  have hprev := st177_p207
  have hstep := st177_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p209 : ((20047033903/15625000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT177 (i+1))
      = (∑ i ∈ Finset.range 208, stT177 (i+1)) + stT177 209 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 208
    simpa using h
  have hprev := st177_p208
  have hstep := st177_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p210 : ((642720565387/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT177 (i+1))
      = (∑ i ∈ Finset.range 209, stT177 (i+1)) + stT177 210 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 209
    simpa using h
  have hprev := st177_p209
  have hstep := st177_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p211 : ((334581972701/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT177 (i+1))
      = (∑ i ∈ Finset.range 210, stT177 (i+1)) + stT177 211 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 210
    simpa using h
  have hprev := st177_p210
  have hstep := st177_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p212 : ((3515778153737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT177 (i+1))
      = (∑ i ∈ Finset.range 211, stT177 (i+1)) + stT177 212 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 211
    simpa using h
  have hprev := st177_p211
  have hstep := st177_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p213 : ((56435513417/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT177 (i+1))
      = (∑ i ∈ Finset.range 212, stT177 (i+1)) + stT177 213 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 212
    simpa using h
  have hprev := st177_p212
  have hstep := st177_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p214 : ((7144670881447/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT177 (i+1))
      = (∑ i ∈ Finset.range 213, stT177 (i+1)) + stT177 214 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 213
    simpa using h
  have hprev := st177_p213
  have hstep := st177_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p215 : ((6847417904737/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT177 (i+1))
      = (∑ i ∈ Finset.range 214, stT177 (i+1)) + stT177 215 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 214
    simpa using h
  have hprev := st177_p214
  have hstep := st177_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p216 : ((6523321747429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT177 (i+1))
      = (∑ i ∈ Finset.range 215, stT177 (i+1)) + stT177 216 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 215
    simpa using h
  have hprev := st177_p215
  have hstep := st177_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p217 : ((6377471899179/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT177 (i+1))
      = (∑ i ∈ Finset.range 216, stT177 (i+1)) + stT177 217 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 216
    simpa using h
  have hprev := st177_p216
  have hstep := st177_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p218 : ((1624953657431/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT177 (i+1))
      = (∑ i ∈ Finset.range 217, stT177 (i+1)) + stT177 218 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 217
    simpa using h
  have hprev := st177_p217
  have hstep := st177_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p219 : ((1362432514089/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT177 (i+1))
      = (∑ i ∈ Finset.range 218, stT177 (i+1)) + stT177 219 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 218
    simpa using h
  have hprev := st177_p218
  have hstep := st177_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p220 : ((7120584341781/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT177 (i+1))
      = (∑ i ∈ Finset.range 219, stT177 (i+1)) + stT177 220 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 219
    simpa using h
  have hprev := st177_p219
  have hstep := st177_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p221 : ((289470245661/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT177 (i+1))
      = (∑ i ∈ Finset.range 220, stT177 (i+1)) + stT177 221 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 220
    simpa using h
  have hprev := st177_p220
  have hstep := st177_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p222 : ((14183748973341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT177 (i+1))
      = (∑ i ∈ Finset.range 221, stT177 (i+1)) + stT177 222 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 221
    simpa using h
  have hprev := st177_p221
  have hstep := st177_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p223 : ((13549965427341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT177 (i+1))
      = (∑ i ∈ Finset.range 222, stT177 (i+1)) + stT177 223 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 222
    simpa using h
  have hprev := st177_p222
  have hstep := st177_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p224 : ((12952131295071/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT177 (i+1))
      = (∑ i ∈ Finset.range 223, stT177 (i+1)) + stT177 224 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 223
    simpa using h
  have hprev := st177_p223
  have hstep := st177_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p225 : ((12742803190407/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT177 (i+1))
      = (∑ i ∈ Finset.range 224, stT177 (i+1)) + stT177 225 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 224
    simpa using h
  have hprev := st177_p224
  have hstep := st177_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p226 : ((13041397003557/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT177 (i+1))
      = (∑ i ∈ Finset.range 225, stT177 (i+1)) + stT177 226 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 225
    simpa using h
  have hprev := st177_p225
  have hstep := st177_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p227 : ((2734120750533/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT177 (i+1))
      = (∑ i ∈ Finset.range 226, stT177 (i+1)) + stT177 227 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 226
    simpa using h
  have hprev := st177_p226
  have hstep := st177_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p228 : ((570626917319/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT177 (i+1))
      = (∑ i ∈ Finset.range 227, stT177 (i+1)) + stT177 228 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 227
    simpa using h
  have hprev := st177_p227
  have hstep := st177_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p229 : ((14487204898477/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT177 (i+1))
      = (∑ i ∈ Finset.range 228, stT177 (i+1)) + stT177 229 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 228
    simpa using h
  have hprev := st177_p228
  have hstep := st177_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p230 : ((2842539335121/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT177 (i+1))
      = (∑ i ∈ Finset.range 229, stT177 (i+1)) + stT177 230 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 229
    simpa using h
  have hprev := st177_p229
  have hstep := st177_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p231 : ((13600090069493/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT177 (i+1))
      = (∑ i ∈ Finset.range 230, stT177 (i+1)) + stT177 231 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 230
    simpa using h
  have hprev := st177_p230
  have hstep := st177_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p232 : ((12993074101419/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT177 (i+1))
      = (∑ i ∈ Finset.range 231, stT177 (i+1)) + stT177 232 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 231
    simpa using h
  have hprev := st177_p231
  have hstep := st177_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p233 : ((2545361001099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT177 (i+1))
      = (∑ i ∈ Finset.range 232, stT177 (i+1)) + stT177 233 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 232
    simpa using h
  have hprev := st177_p232
  have hstep := st177_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p234 : ((2588898753099/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT177 (i+1))
      = (∑ i ∈ Finset.range 233, stT177 (i+1)) + stT177 234 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 233
    simpa using h
  have hprev := st177_p233
  have hstep := st177_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p235 : ((13524135465767/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT177 (i+1))
      = (∑ i ∈ Finset.range 234, stT177 (i+1)) + stT177 235 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 234
    simpa using h
  have hprev := st177_p234
  have hstep := st177_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p236 : ((14150564263783/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT177 (i+1))
      = (∑ i ∈ Finset.range 235, stT177 (i+1)) + stT177 236 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 235
    simpa using h
  have hprev := st177_p235
  have hstep := st177_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p237 : ((5795412187/4000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT177 (i+1))
      = (∑ i ∈ Finset.range 236, stT177 (i+1)) + stT177 237 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 236
    simpa using h
  have hprev := st177_p236
  have hstep := st177_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p238 : ((3590246813911/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT177 (i+1))
      = (∑ i ∈ Finset.range 237, stT177 (i+1)) + stT177 238 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 237
    simpa using h
  have hprev := st177_p237
  have hstep := st177_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p239 : ((3459632880283/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT177 (i+1))
      = (∑ i ∈ Finset.range 238, stT177 (i+1)) + stT177 239 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 238
    simpa using h
  have hprev := st177_p238
  have hstep := st177_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p240 : ((6598394836997/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT177 (i+1))
      = (∑ i ∈ Finset.range 239, stT177 (i+1)) + stT177 240 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 239
    simpa using h
  have hprev := st177_p239
  have hstep := st177_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p241 : ((2553780775529/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT177 (i+1))
      = (∑ i ∈ Finset.range 240, stT177 (i+1)) + stT177 241 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 240
    simpa using h
  have hprev := st177_p240
  have hstep := st177_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p242 : ((12773043021381/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT177 (i+1))
      = (∑ i ∈ Finset.range 241, stT177 (i+1)) + stT177 242 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 241
    simpa using h
  have hprev := st177_p241
  have hstep := st177_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p243 : ((13203850685881/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT177 (i+1))
      = (∑ i ∈ Finset.range 242, stT177 (i+1)) + stT177 243 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 242
    simpa using h
  have hprev := st177_p242
  have hstep := st177_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p244 : ((13840306894449/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT177 (i+1))
      = (∑ i ∈ Finset.range 243, stT177 (i+1)) + stT177 244 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 243
    simpa using h
  have hprev := st177_p243
  have hstep := st177_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p245 : ((14361570933857/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT177 (i+1))
      = (∑ i ∈ Finset.range 244, stT177 (i+1)) + stT177 245 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 244
    simpa using h
  have hprev := st177_p244
  have hstep := st177_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p246 : ((14509002095369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT177 (i+1))
      = (∑ i ∈ Finset.range 245, stT177 (i+1)) + stT177 246 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 245
    simpa using h
  have hprev := st177_p245
  have hstep := st177_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p247 : ((7106262231667/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT177 (i+1))
      = (∑ i ∈ Finset.range 246, stT177 (i+1)) + stT177 247 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 246
    simpa using h
  have hprev := st177_p246
  have hstep := st177_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p248 : ((3405173025329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT177 (i+1))
      = (∑ i ∈ Finset.range 247, stT177 (i+1)) + stT177 248 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 247
    simpa using h
  have hprev := st177_p247
  have hstep := st177_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p249 : ((13023482969541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT177 (i+1))
      = (∑ i ∈ Finset.range 248, stT177 (i+1)) + stT177 249 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 248
    simpa using h
  have hprev := st177_p248
  have hstep := st177_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_p250 : ((12709147277893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT177 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT177 (i+1))
      = (∑ i ∈ Finset.range 249, stT177 (i+1)) + stT177 250 := by
    have h := Finset.sum_range_succ (fun i => stT177 (i+1)) 249
    simpa using h
  have hprev := st177_p249
  have hstep := st177_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st177_s250 :
    |Real.sin (((177 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))
      - ((-34711/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -2613607/5000000) (δ := 4511/500000000) (ψ := -393717/500000) 177 156
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 177`** (evaluated boundary). -/
theorem station_177_sign : 0 < hardyG ((((177:ℕ)):ℝ)) := by
  have hcore := phase_station_lower_eval 177 250 (by norm_num) (by norm_num)
    ((-393717/500000 : ℚ) : ℝ)
  have hchain := st177_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT177 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((177 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-393717/500000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st177_c250
  have hsinb := abs_le.mp st177_s250
  have hbdy_lo : ((19458841521489/250634000000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((177 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-393717/500000 : ℚ) : ℝ))) / 2
          - ((((177:ℕ)):ℝ))
            * Real.sin (((177 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-393717/500000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((177:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((177:ℝ) * Real.log (250:ℝ) - ((-393717/500000 : ℚ) : ℝ))) / 2
        - ((177:ℝ)) * Real.sin ((177:ℝ) * Real.log (250:ℝ) - ((-393717/500000 : ℚ) : ℝ))
        ≥ ((153835779/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((177:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((153835779/1000000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((153835779/1000000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((153835779/1000000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((177:ℕ)):ℝ))+1) * (((((177:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((663153279701/937500000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((12709147277893/10000000000000 : ℚ) : ℝ) + ((19458841521489/250634000000000 : ℚ) : ℝ)
      - ((663153279701/937500000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-393717/500000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((177:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-393717/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((177:ℕ)):ℝ)))).re
      - Real.sin ((-393717/500000 : ℚ) : ℝ)
        * (riemannZeta (line ((((177:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((177:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((177:ℕ)):ℝ))
      = (((((177:ℕ)):ℝ)) * (Real.log ((((177:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((177:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_177
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
  have hθwin : |(((-393717/500000 : ℚ) : ℝ) + ((33:ℤ)) * (2*Real.pi)) - theta ((((177:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((177:ℕ)):ℝ)))
    (φ := ((-393717/500000 : ℚ) : ℝ) + ((33:ℤ)) * (2*Real.pi)) hθwin).1
  apply hprox
  rw [(cos_sin_shift (((-393717/500000 : ℚ)) : ℝ) 33).1,
    (cos_sin_shift (((-393717/500000 : ℚ)) : ℝ) 33).2]
  exact hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_177_sign
end AxiomAudit
