import RequestProject.DVPSqrt250Table
import RequestProject.DVPLog250Table
import RequestProject.DVPSqrt200Table
import RequestProject.DVPLog200Table
import RequestProject.DVPPhaseStationEval

/-!
# Station `t = 226` (rung-235.5; evaluated boundary, N = 250)
-/

open Complex Finset
open CriticalLinePhasor.ContourArgument CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The station term (opaque under `simp`/`norm_num`). -/
noncomputable def stT226 (n : ℕ) : ℝ :=
  ((n : ℕ) : ℝ) ^ (-(1/2 : ℝ))
    * Real.cos (((226 : ℕ) : ℝ) * Real.log ((n : ℕ)) - ((-35361/50000 : ℚ) : ℝ))

theorem st226_c1 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((760171/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 35361/200000) (δ := 1/1000000000) (ψ := -35361/50000) 226 0
    (log_br_1).1 (log_br_1).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t1 : ((760121/1000000 : ℚ) : ℝ) ≤ stT226 1 := by
  have hc : ((760121/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((1 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c1).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_1).1
  have hw2 : ((1 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((760121/1000000 : ℚ) : ℝ)
      = ((1 : ℚ) : ℝ) * ((760121/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c2 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((480687/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 174277/2500000) (δ := 5661/500000000) (ψ := -35361/50000) 226 25
    (log_br_2).1 (log_br_2).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t2 : ((1699396603177/2500000000000 : ℚ) : ℝ) ≤ stT226 2 := by
  have hc : ((240331/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((2 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c2).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_2).1
  have hw2 : ((2 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((7071067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1699396603177/2500000000000 : ℚ) : ℝ)
      = ((7071067/10000000 : ℚ) : ℝ) * ((240331/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c3 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-691113/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5834559/10000000) (δ := 11489/1000000000) (ψ := -35361/50000) 226 40
    (log_br_3).1 (log_br_3).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t3 : ((-3990431653989/10000000000000 : ℚ) : ℝ) ≤ stT226 3 := by
  have hc : ((-691163/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((3 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c3).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_3).2
  have h0 : (0:ℝ) ≤ ((3 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3990431653989/10000000000000 : ℚ) : ℝ)
      = ((5773503/10000000 : ℚ) : ℝ) * ((-691163/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c4 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((494421/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -186903/5000000) (δ := 11443/1000000000) (ψ := -35361/50000) 226 50
    (log_br_4).1 (log_br_4).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t4 : ((123599/250000 : ℚ) : ℝ) ≤ stT226 4 := by
  have hc : ((123599/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((4 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c4).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_4).1
  have hw2 : ((4 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/2 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((123599/250000 : ℚ) : ℝ)
      = ((1/2 : ℚ) : ℝ) * ((123599/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c5 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((999881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 19311/5000000) (δ := 2277/200000000) (ψ := -35361/50000) 226 58
    (log_br_5).1 (log_br_5).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t5 : ((894275841837/2000000000000 : ℚ) : ℝ) ≤ stT226 5 := by
  have hc : ((999831/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((5 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c5).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_5).1
  have hw2 : ((5 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((894275841837/2000000000000 : ℚ) : ℝ)
      = ((894427/2000000 : ℚ) : ℝ) * ((999831/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c6 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-464443/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6905473/10000000) (δ := 1421/125000000) (ψ := -35361/50000) 226 65
    (log_br_6).1 (log_br_6).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t6 : ((-474045678511/1250000000000 : ℚ) : ℝ) ≤ stT226 6 := by
  have hc : ((-116117/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((6 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c6).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_6).2
  have h0 : (0:ℝ) ≤ ((6 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-474045678511/1250000000000 : ℚ) : ℝ)
      = ((4082483/10000000 : ℚ) : ℝ) * ((-116117/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c7 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((197507/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25779/156250) (δ := 1413/125000000) (ψ := -35361/50000) 226 70
    (log_br_7).1 (log_br_7).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t7 : ((373229450979/1250000000000 : ℚ) : ℝ) ≤ stT226 7 := by
  have hc : ((394989/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((7 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c7).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_7).1
  have hw2 : ((7 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((373229450979/1250000000000 : ℚ) : ℝ)
      = ((944911/2500000 : ℚ) : ℝ) * ((394989/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c8 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((418809/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1444719/10000000) (δ := 143/12500000) (ψ := -35361/50000) 226 75
    (log_br_8).1 (log_br_8).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t8 : ((46269520371/156250000000 : ℚ) : ℝ) ≤ stT226 8 := by
  have hc : ((13087/15625 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((8 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c8).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_8).1
  have hw2 : ((8 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3535533/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46269520371/156250000000 : ℚ) : ℝ)
      = ((3535533/10000000 : ℚ) : ℝ) * ((13087/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c9 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((76883/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2270823/10000000) (δ := 11469/1000000000) (ψ := -35361/50000) 226 79
    (log_br_9).1 (log_br_9).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t9 : ((1025023230831/5000000000000 : ℚ) : ℝ) ≤ stT226 9 := by
  have hc : ((307507/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((9 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c9).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_9).1
  have hw2 : ((9 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3333333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1025023230831/5000000000000 : ℚ) : ℝ)
      = ((3333333/10000000 : ℚ) : ℝ) * ((307507/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c10 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((183189/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -258087/2500000) (δ := 5653/500000000) (ψ := -35361/50000) 226 83
    (log_br_10).1 (log_br_10).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t10 : ((579262738583/2000000000000 : ℚ) : ℝ) ≤ stT226 10 := by
  have hc : ((183179/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((10 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c10).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_10).1
  have hw2 : ((10 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((3162277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((579262738583/2000000000000 : ℚ) : ℝ)
      = ((3162277/10000000 : ℚ) : ℝ) * ((183179/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c11 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-324707/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 227761/400000) (δ := 1423/125000000) (ψ := -35361/50000) 226 86
    (log_br_11).1 (log_br_11).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t11 : ((-122387999931/625000000000 : ℚ) : ℝ) ≤ stT226 11 := by
  have hc : ((-81183/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((11 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c11).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_11).2
  have h0 : (0:ℝ) ≤ ((11 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122387999931/625000000000 : ℚ) : ℝ)
      = ((1507557/5000000 : ℚ) : ℝ) * ((-81183/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c12 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-499401/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 966447/1250000) (δ := 11463/1000000000) (ψ := -35361/50000) 226 89
    (log_br_12).1 (log_br_12).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t12 : ((-22526859443/78125000000 : ℚ) : ℝ) ≤ stT226 12 := by
  have hc : ((-249713/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((12 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c12).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_12).2
  have h0 : (0:ℝ) ≤ ((12 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-22526859443/78125000000 : ℚ) : ℝ)
      = ((90211/312500 : ℚ) : ℝ) * ((-249713/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c13 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-345159/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1457953/2500000) (δ := 11341/1000000000) (ψ := -35361/50000) 226 92
    (log_br_13).1 (log_br_13).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t13 : ((-29917755287/156250000000 : ℚ) : ℝ) ≤ stT226 13 := by
  have hc : ((-10787/15625 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((13 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c13).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_13).2
  have h0 : (0:ℝ) ≤ ((13 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29917755287/156250000000 : ℚ) : ℝ)
      = ((2773501/10000000 : ℚ) : ℝ) * ((-10787/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c14 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((486653/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 289471/5000000) (δ := 11419/1000000000) (ψ := -35361/50000) 226 95
    (log_br_14).1 (log_br_14).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t14 : ((81285489521/312500000000 : ℚ) : ℝ) ≤ stT226 14 := by
  have hc : ((121657/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((14 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c14).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_14).1
  have hw2 : ((14 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((81285489521/312500000000 : ℚ) : ℝ)
      = ((668153/2500000 : ℚ) : ℝ) * ((121657/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c15 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-496639/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7563959/10000000) (δ := 2261/200000000) (ψ := -35361/50000) 226 98
    (log_br_15).1 (log_br_15).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t15 : ((-160297623087/625000000000 : ℚ) : ℝ) ≤ stT226 15 := by
  have hc : ((-62083/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((15 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c15).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_15).2
  have h0 : (0:ℝ) ≤ ((15 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160297623087/625000000000 : ℚ) : ℝ)
      = ((2581989/10000000 : ℚ) : ℝ) * ((-62083/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c16 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((53503/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2515633/10000000) (δ := 11319/1000000000) (ψ := -35361/50000) 226 100
    (log_br_16).1 (log_br_16).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t16 : ((26749/200000 : ℚ) : ℝ) ≤ stT226 16 := by
  have hc : ((26749/50000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((16 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c16).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_16).1
  have hw2 : ((16 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/4 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((26749/200000 : ℚ) : ℝ)
      = ((1/4 : ℚ) : ℝ) * ((26749/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c17 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((991751/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 321339/10000000) (δ := 11469/1000000000) (ψ := -35361/50000) 226 102
    (log_br_17).1 (log_br_17).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t17 : ((601306992639/2500000000000 : ℚ) : ℝ) ≤ stT226 17 := by
  have hc : ((991701/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((17 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c17).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_17).1
  have hw2 : ((17 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((601306992639/2500000000000 : ℚ) : ℝ)
      = ((606339/2500000 : ℚ) : ℝ) * ((991701/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c18 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((221753/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1199909/10000000) (δ := 2837/250000000) (ψ := -35361/50000) 226 104
    (log_br_18).1 (log_br_18).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t18 : ((522647236791/2500000000000 : ℚ) : ℝ) ≤ stT226 18 := by
  have hc : ((443481/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((18 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c18).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_18).1
  have hw2 : ((18 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((522647236791/2500000000000 : ℚ) : ℝ)
      = ((1178511/5000000 : ℚ) : ℝ) * ((443481/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c19 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((495599/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6639/200000) (δ := 143/12500000) (ψ := -35361/50000) 226 106
    (log_br_19).1 (log_br_19).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t19 : ((568462280559/2500000000000 : ℚ) : ℝ) ≤ stT226 19 := by
  have hc : ((247787/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((19 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c19).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_19).1
  have hw2 : ((19 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2294157/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((568462280559/2500000000000 : ℚ) : ℝ)
      = ((2294157/10000000 : ℚ) : ℝ) * ((247787/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c20 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((666491/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1051631/5000000) (δ := 5713/500000000) (ψ := -35361/50000) 226 108
    (log_br_20).1 (log_br_20).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t20 : ((1490206727547/10000000000000 : ℚ) : ℝ) ≤ stT226 20 := by
  have hc : ((666441/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((20 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c20).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_20).1
  have hw2 : ((20 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((2236067/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1490206727547/10000000000000 : ℚ) : ℝ)
      = ((2236067/10000000 : ℚ) : ℝ) * ((666441/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c21 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-72449/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -238109/400000) (δ := 11391/1000000000) (ψ := -35361/50000) 226 110
    (log_br_21).1 (log_br_21).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t21 : ((-79053798633/500000000000 : ℚ) : ℝ) ≤ stT226 21 := by
  have hc : ((-36227/50000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((21 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c21).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_21).2
  have h0 : (0:ℝ) ≤ ((21 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-79053798633/500000000000 : ℚ) : ℝ)
      = ((2182179/10000000 : ℚ) : ℝ) * ((-36227/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c22 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-17179/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 577889/1250000) (δ := 5749/500000000) (ψ := -35361/50000) 226 111
    (log_br_22).1 (log_br_22).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t22 : ((-36632427957/625000000000 : ℚ) : ℝ) ≤ stT226 22 := by
  have hc : ((-137457/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((22 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c22).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_22).2
  have h0 : (0:ℝ) ≤ ((22 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36632427957/625000000000 : ℚ) : ℝ)
      = ((266501/1250000 : ℚ) : ℝ) * ((-137457/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c23 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((195797/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -419387/2500000) (δ := 11313/1000000000) (ψ := -35361/50000) 226 113
    (log_br_23).1 (log_br_23).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t23 : ((102059718867/625000000000 : ℚ) : ℝ) ≤ stT226 23 := by
  have hc : ((391569/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((23 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c23).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_23).1
  have hw2 : ((23 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((102059718867/625000000000 : ℚ) : ℝ)
      = ((260643/1250000 : ℚ) : ℝ) * ((391569/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c24 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-444113/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6660663/10000000) (δ := 571/50000000) (ψ := -35361/50000) 226 114
    (log_br_24).1 (log_br_24).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t24 : ((-226648284849/1250000000000 : ℚ) : ℝ) ≤ stT226 24 := by
  have hc : ((-222069/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((24 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c24).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_24).2
  have h0 : (0:ℝ) ≤ ((24 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226648284849/1250000000000 : ℚ) : ℝ)
      = ((1020621/5000000 : ℚ) : ℝ) * ((-222069/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c25 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((779873/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -845417/5000000) (δ := 11369/1000000000) (ψ := -35361/50000) 226 116
    (log_br_25).1 (log_br_25).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t25 : ((779823/5000000 : ℚ) : ℝ) ≤ stT226 25 := by
  have hc : ((779823/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((25 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c25).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_25).1
  have hw2 : ((25 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1/5 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((779823/5000000 : ℚ) : ℝ)
      = ((1/5 : ℚ) : ℝ) * ((779823/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c26 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-81853/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2380449/5000000) (δ := 11461/1000000000) (ψ := -35361/50000) 226 117
    (log_br_26).1 (log_br_26).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t26 : ((-160551507711/2500000000000 : ℚ) : ℝ) ≤ stT226 26 := by
  have hc : ((-163731/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((26 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c26).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_26).2
  have h0 : (0:ℝ) ≤ ((26 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-160551507711/2500000000000 : ℚ) : ℝ)
      = ((980581/5000000 : ℚ) : ℝ) * ((-163731/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c27 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-532801/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5331759/10000000) (δ := 11447/1000000000) (ψ := -35361/50000) 226 119
    (log_br_27).1 (log_br_27).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t27 : ((-1025472282351/10000000000000 : ℚ) : ℝ) ≤ stT226 27 := by
  have hc : ((-532851/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((27 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c27).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_27).2
  have h0 : (0:ℝ) ≤ ((27 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1025472282351/10000000000000 : ℚ) : ℝ)
      = ((1924501/10000000 : ℚ) : ℝ) * ((-532851/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c28 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((9807/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -491971/10000000) (δ := 11463/1000000000) (ψ := -35361/50000) 226 120
    (log_br_28).1 (log_br_28).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t28 : ((18532539443/100000000000 : ℚ) : ℝ) ≤ stT226 28 := by
  have hc : ((19613/20000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((28 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c28).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_28).1
  have hw2 : ((28 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18532539443/100000000000 : ℚ) : ℝ)
      = ((944911/5000000 : ℚ) : ℝ) * ((19613/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c29 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((14981/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 72533/200000) (δ := 1137/100000000) (ψ := -35361/50000) 226 121
    (log_br_29).1 (log_br_29).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t29 : ((111229627747/5000000000000 : ℚ) : ℝ) ≤ stT226 29 := by
  have hc : ((59899/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((29 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c29).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_29).1
  have hw2 : ((29 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1856953/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((111229627747/5000000000000 : ℚ) : ℝ)
      = ((1856953/10000000 : ℚ) : ℝ) * ((59899/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c30 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-190321/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3536517/5000000) (δ := 5663/500000000) (ψ := -35361/50000) 226 122
    (log_br_30).1 (log_br_30).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t30 : ((-173747650301/1000000000000 : ℚ) : ℝ) ≤ stT226 30 := by
  have hc : ((-190331/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((30 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c30).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_30).2
  have h0 : (0:ℝ) ≤ ((30 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-173747650301/1000000000000 : ℚ) : ℝ)
      = ((912871/5000000 : ℚ) : ℝ) * ((-190331/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c31 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-685903/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5816599/10000000) (δ := 11311/1000000000) (ψ := -35361/50000) 226 124
    (log_br_31).1 (log_br_31).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t31 : ((-616004314731/5000000000000 : ℚ) : ℝ) ≤ stT226 31 := by
  have hc : ((-685953/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((31 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c31).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_31).2
  have h0 : (0:ℝ) ≤ ((31 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-616004314731/5000000000000 : ℚ) : ℝ)
      = ((898027/5000000 : ℚ) : ℝ) * ((-685953/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c32 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((135757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3586547/10000000) (δ := 2851/250000000) (ψ := -35361/50000) 226 125
    (log_br_32).1 (log_br_32).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t32 : ((119949110281/5000000000000 : ℚ) : ℝ) ≤ stT226 32 := by
  have hc : ((135707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((32 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c32).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_32).1
  have hw2 : ((32 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((883883/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((119949110281/5000000000000 : ℚ) : ℝ)
      = ((883883/5000000 : ℚ) : ℝ) * ((135707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c33 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((361237/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -477139/2500000) (δ := 5653/500000000) (ψ := -35361/50000) 226 126
    (log_br_33).1 (log_br_33).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t33 : ((19649661891/156250000000 : ℚ) : ℝ) ≤ stT226 33 := by
  have hc : ((90303/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((33 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c33).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_33).1
  have hw2 : ((33 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((217597/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((19649661891/156250000000 : ℚ) : ℝ)
      = ((217597/1250000 : ℚ) : ℝ) * ((90303/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c34 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((955387/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -374787/5000000) (δ := 11413/1000000000) (ψ := -35361/50000) 226 127
    (log_br_34).1 (log_br_34).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t34 : ((327677724989/2000000000000 : ℚ) : ℝ) ≤ stT226 34 := by
  have hc : ((955337/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((34 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c34).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_34).1
  have hw2 : ((34 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((342997/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((327677724989/2000000000000 : ℚ) : ℝ)
      = ((342997/2000000 : ℚ) : ℝ) * ((955337/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c35 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((999493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -199/25000) (δ := 283/25000000) (ψ := -35361/50000) 226 128
    (log_br_35).1 (log_br_35).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t35 : ((422341624611/2500000000000 : ℚ) : ℝ) ≤ stT226 35 := by
  have hc : ((999443/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((35 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c35).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_35).1
  have hw2 : ((35 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((422341624611/2500000000000 : ℚ) : ℝ)
      = ((422577/2500000 : ℚ) : ℝ) * ((999443/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c36 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((998669/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 25799/2000000) (δ := 91/8000000) (ψ := -35361/50000) 226 129
    (log_br_36).1 (log_br_36).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t36 : ((832182167127/5000000000000 : ℚ) : ℝ) ≤ stT226 36 := by
  have hc : ((998619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((36 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c36).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_36).1
  have hw2 : ((36 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((832182167127/5000000000000 : ℚ) : ℝ)
      = ((833333/5000000 : ℚ) : ℝ) * ((998619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c37 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((999223/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98533/10000000) (δ := 2267/200000000) (ψ := -35361/50000) 226 130
    (log_br_37).1 (log_br_37).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t37 : ((1642629421097/10000000000000 : ℚ) : ℝ) ≤ stT226 37 := by
  have hc : ((999173/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((37 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c37).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_37).1
  have hw2 : ((37 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1643989/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1642629421097/10000000000000 : ℚ) : ℝ)
      = ((1643989/10000000 : ℚ) : ℝ) * ((999173/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c38 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((119579/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -738963/10000000) (δ := 5721/500000000) (ψ := -35361/50000) 226 131
    (log_br_38).1 (log_br_38).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t38 : ((387945178137/2500000000000 : ℚ) : ℝ) ≤ stT226 38 := by
  have hc : ((478291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((38 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c38).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_38).1
  have hw2 : ((38 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((387945178137/2500000000000 : ℚ) : ℝ)
      = ((811107/5000000 : ℚ) : ℝ) * ((478291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c39 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((94933/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1770769/10000000) (δ := 11349/1000000000) (ψ := -35361/50000) 226 132
    (log_br_39).1 (log_br_39).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t39 : ((608017604667/5000000000000 : ℚ) : ℝ) ≤ stT226 39 := by
  have hc : ((379707/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((39 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c39).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_39).1
  have hw2 : ((39 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1601281/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((608017604667/5000000000000 : ℚ) : ℝ)
      = ((1601281/10000000 : ℚ) : ℝ) * ((379707/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c40 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((74149/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -126967/400000) (δ := 179/15625000) (ψ := -35361/50000) 226 133
    (log_br_40).1 (log_br_40).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t40 : ((117220037337/2500000000000 : ℚ) : ℝ) ≤ stT226 40 := by
  have hc : ((148273/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((40 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c40).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_40).1
  have hw2 : ((40 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((790569/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((117220037337/2500000000000 : ℚ) : ℝ)
      = ((790569/5000000 : ℚ) : ℝ) * ((148273/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c41 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-390829/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -246541/500000) (δ := 11439/1000000000) (ψ := -35361/50000) 226 134
    (log_br_41).1 (log_br_41).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t41 : ((-305225293851/5000000000000 : ℚ) : ℝ) ≤ stT226 41 := by
  have hc : ((-390879/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((41 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c41).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_41).2
  have h0 : (0:ℝ) ≤ ((41 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-305225293851/5000000000000 : ℚ) : ℝ)
      = ((780869/5000000 : ℚ) : ℝ) * ((-390879/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c42 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-236337/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7023639/10000000) (δ := 2833/250000000) (ψ := -35361/50000) 226 135
    (log_br_42).1 (log_br_42).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t42 : ((-364695314383/2500000000000 : ℚ) : ℝ) ≤ stT226 42 := by
  have hc : ((-472699/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((42 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c42).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_42).2
  have h0 : (0:ℝ) ≤ ((42 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-364695314383/2500000000000 : ℚ) : ℝ)
      = ((771517/5000000 : ℚ) : ℝ) * ((-472699/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c43 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-161233/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3135547/5000000) (δ := 11471/1000000000) (ψ := -35361/50000) 226 135
    (log_br_43).1 (log_br_43).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t43 : ((-122946658799/1000000000000 : ℚ) : ℝ) ≤ stT226 43 := by
  have hc : ((-161243/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((43 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c43).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_43).2
  have h0 : (0:ℝ) ≤ ((43 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-122946658799/1000000000000 : ℚ) : ℝ)
      = ((762493/5000000 : ℚ) : ℝ) * ((-161243/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c44 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((37339/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1776099/5000000) (δ := 5689/500000000) (ψ := -35361/50000) 226 136
    (log_br_44).1 (log_br_44).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t44 : ((28135894517/1250000000000 : ℚ) : ℝ) ≤ stT226 44 := by
  have hc : ((74653/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((44 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c44).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_44).1
  have hw2 : ((44 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((28135894517/1250000000000 : ℚ) : ℝ)
      = ((376889/2500000 : ℚ) : ℝ) * ((74653/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c45 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((195329/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 541367/10000000) (δ := 2297/200000000) (ψ := -35361/50000) 226 137
    (log_br_45).1 (log_br_45).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t45 : ((291164181809/2000000000000 : ℚ) : ℝ) ≤ stT226 45 := by
  have hc : ((195319/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((45 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c45).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_45).1
  have hw2 : ((45 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1490711/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((291164181809/2000000000000 : ℚ) : ℝ)
      = ((1490711/10000000 : ℚ) : ℝ) * ((195319/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c46 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((113531/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1374259/5000000) (δ := 89/7812500) (ψ := -35361/50000) 226 138
    (log_br_46).1 (log_br_46).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t46 : ((334747666503/5000000000000 : ℚ) : ℝ) ≤ stT226 46 := by
  have hc : ((227037/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((46 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c46).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_46).1
  have hw2 : ((46 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1474419/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((334747666503/5000000000000 : ℚ) : ℝ)
      = ((1474419/10000000 : ℚ) : ℝ) * ((227037/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c47 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-814213/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3152711/5000000) (δ := 1413/125000000) (ψ := -35361/50000) 226 139
    (log_br_47).1 (log_br_47).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t47 : ((-23754494499/200000000000 : ℚ) : ℝ) ≤ stT226 47 := by
  have hc : ((-814263/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((47 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c47).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_47).2
  have h0 : (0:ℝ) ≤ ((47 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23754494499/200000000000 : ℚ) : ℝ)
      = ((29173/200000 : ℚ) : ℝ) * ((-814263/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c48 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-30857/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5589749/10000000) (δ := 1413/125000000) (ψ := -35361/50000) 226 139
    (log_br_48).1 (log_br_48).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t48 : ((-5567732709/62500000000 : ℚ) : ℝ) ≤ stT226 48 := by
  have hc : ((-61719/100000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((48 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c48).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_48).2
  have h0 : (0:ℝ) ≤ ((48 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5567732709/62500000000 : ℚ) : ℝ)
      = ((90211/625000 : ℚ) : ℝ) * ((-61719/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c49 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((1309/1600 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 765817/5000000) (δ := 11407/1000000000) (ψ := -35361/50000) 226 140
    (log_br_49).1 (log_br_49).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t49 : ((46747128833/400000000000 : ℚ) : ℝ) ≤ stT226 49 := by
  have hc : ((32723/40000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((49 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c49).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_49).1
  have hw2 : ((49 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1428571/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46747128833/400000000000 : ℚ) : ℝ)
      = ((1428571/10000000 : ℚ) : ℝ) * ((32723/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c50 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((449403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -690437/2500000) (δ := 11489/1000000000) (ψ := -35361/50000) 226 141
    (log_br_50).1 (log_br_50).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t50 : ((635480854189/10000000000000 : ℚ) : ℝ) ≤ stT226 50 := by
  have hc : ((449353/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((50 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c50).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_50).1
  have hw2 : ((50 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1414213/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((635480854189/10000000000000 : ℚ) : ℝ)
      = ((1414213/10000000 : ℚ) : ℝ) * ((449353/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c51 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-60867/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3640621/5000000) (δ := 5691/500000000) (ψ := -35361/50000) 226 142
    (log_br_51).1 (log_br_51).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t51 : ((-681882236041/5000000000000 : ℚ) : ℝ) ≤ stT226 51 := by
  have hc : ((-486961/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((51 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c51).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_51).2
  have h0 : (0:ℝ) ≤ ((51 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-681882236041/5000000000000 : ℚ) : ℝ)
      = ((1400281/10000000 : ℚ) : ℝ) * ((-486961/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c52 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((4733/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 737997/2000000) (δ := 11421/1000000000) (ψ := -35361/50000) 226 142
    (log_br_52).1 (log_br_52).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t52 : ((52480167/4000000000 : ℚ) : ℝ) ≤ stT226 52 := by
  have hc : ((9461/100000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((52 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c52).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_52).1
  have hw2 : ((52 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/40000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((52480167/4000000000 : ℚ) : ℝ)
      = ((5547/40000 : ℚ) : ℝ) * ((9461/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c53 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((438239/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627873/5000000) (δ := 459/40000000) (ψ := -35361/50000) 226 143
    (log_br_53).1 (log_br_53).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t53 : ((60193294147/500000000000 : ℚ) : ℝ) ≤ stT226 53 := by
  have hc : ((219107/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((53 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c53).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_53).1
  have hw2 : ((53 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((274721/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((60193294147/500000000000 : ℚ) : ℝ)
      = ((274721/2000000 : ℚ) : ℝ) * ((219107/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c54 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-33447/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -400167/625000) (δ := 2287/200000000) (ψ := -35361/50000) 226 144
    (log_br_54).1 (log_br_54).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t54 : ((-11379583943/100000000000 : ℚ) : ℝ) ≤ stT226 54 := by
  have hc : ((-33449/40000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((54 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c54).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_54).2
  have h0 : (0:ℝ) ≤ ((54 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-11379583943/100000000000 : ℚ) : ℝ)
      = ((340207/2500000 : ℚ) : ℝ) * ((-33449/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c55 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-15031/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3964569/10000000) (δ := 1421/125000000) (ψ := -35361/50000) 226 144
    (log_br_55).1 (log_br_55).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t55 : ((-50838051/25000000000 : ℚ) : ℝ) ≤ stT226 55 := by
  have hc : ((-15081/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((55 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c55).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_55).2
  have h0 : (0:ℝ) ≤ ((55 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-50838051/25000000000 : ℚ) : ℝ)
      = ((3371/25000 : ℚ) : ℝ) * ((-15081/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c56 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((40543/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -781471/5000000) (δ := 573/50000000) (ψ := -35361/50000) 226 145
    (log_br_56).1 (log_br_56).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t56 : ((54174513393/500000000000 : ℚ) : ℝ) ≤ stT226 56 := by
  have hc : ((81081/100000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((56 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c56).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_56).1
  have hw2 : ((56 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((54174513393/500000000000 : ℚ) : ℝ)
      = ((668153/5000000 : ℚ) : ℝ) * ((81081/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c57 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-972899/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7270631/10000000) (δ := 11353/1000000000) (ψ := -35361/50000) 226 146
    (log_br_57).1 (log_br_57).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t57 : ((-1288703057817/10000000000000 : ℚ) : ℝ) ≤ stT226 57 := by
  have hc : ((-972949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((57 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c57).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_57).2
  have h0 : (0:ℝ) ≤ ((57 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1288703057817/10000000000000 : ℚ) : ℝ)
      = ((1324533/10000000 : ℚ) : ℝ) * ((-972949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c58 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((521409/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 319467/1250000) (δ := 11353/1000000000) (ψ := -35361/50000) 226 146
    (log_br_58).1 (log_br_58).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t58 : ((85572216747/1250000000000 : ℚ) : ℝ) ≤ stT226 58 := by
  have hc : ((521359/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((58 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c58).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_58).1
  have hw2 : ((58 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85572216747/1250000000000 : ℚ) : ℝ)
      = ((164133/1250000 : ℚ) : ℝ) * ((521359/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c59 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((1379/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3493891/10000000) (δ := 11357/1000000000) (ψ := -35361/50000) 226 147
    (log_br_59).1 (log_br_59).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t59 : ((8973920877/400000000000 : ℚ) : ℝ) ≤ stT226 59 := by
  have hc : ((6893/40000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((59 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c59).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_59).1
  have hw2 : ((59 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1301889/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8973920877/400000000000 : ℚ) : ℝ)
      = ((1301889/10000000 : ℚ) : ℝ) * ((6893/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c60 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-368983/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 150053/250000) (δ := 5723/500000000) (ψ := -35361/50000) 226 147
    (log_br_60).1 (log_br_60).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t60 : ((-5954843537/62500000000 : ℚ) : ℝ) ≤ stT226 60 := by
  have hc : ((-23063/31250 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((60 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c60).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_60).2
  have h0 : (0:ℝ) ≤ ((60 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5954843537/62500000000 : ℚ) : ℝ)
      = ((258199/2000000 : ℚ) : ℝ) * ((-23063/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c61 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((989257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -91697/2500000) (δ := 1433/125000000) (ψ := -35361/50000) 226 148
    (log_br_61).1 (log_br_61).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t61 : ((79159311761/625000000000 : ℚ) : ℝ) ≤ stT226 61 := by
  have hc : ((989207/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((61 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c61).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_61).1
  have hw2 : ((61 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79159311761/625000000000 : ℚ) : ℝ)
      = ((80023/625000 : ℚ) : ℝ) * ((989207/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c62 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-92621/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6887569/10000000) (δ := 11371/1000000000) (ψ := -35361/50000) 226 149
    (log_br_62).1 (log_br_62).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t62 : ((-29408801313/250000000000 : ℚ) : ℝ) ≤ stT226 62 := by
  have hc : ((-46313/50000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((62 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c62).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_62).2
  have h0 : (0:ℝ) ≤ ((62 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-29408801313/250000000000 : ℚ) : ℝ)
      = ((635001/5000000 : ℚ) : ℝ) * ((-46313/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c63 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((40727/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2152657/10000000) (δ := 11371/1000000000) (ψ := -35361/50000) 226 149
    (log_br_63).1 (log_br_63).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t63 : ((410457890871/5000000000000 : ℚ) : ℝ) ≤ stT226 63 := by
  have hc : ((325791/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((63 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c63).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_63).1
  have hw2 : ((63 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1259881/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((410457890871/5000000000000 : ℚ) : ℝ)
      = ((1259881/10000000 : ℚ) : ℝ) * ((325791/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c64 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-28807/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4657517/10000000) (δ := 453/40000000) (ψ := -35361/50000) 226 150
    (log_br_64).1 (log_br_64).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t64 : ((-9003757203/250000000000 : ℚ) : ℝ) ≤ stT226 64 := by
  have hc : ((-7203/25000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((64 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c64).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_64).2
  have h0 : (0:ℝ) ≤ ((64 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9003757203/250000000000 : ℚ) : ℝ)
      = ((1250001/10000000 : ℚ) : ℝ) * ((-7203/25000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c65 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-70089/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1025589/2500000) (δ := 453/40000000) (ψ := -35361/50000) 226 150
    (log_br_65).1 (log_br_65).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t65 : ((-21749192093/2500000000000 : ℚ) : ℝ) ≤ stT226 65 := by
  have hc : ((-70139/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((65 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c65).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_65).2
  have h0 : (0:ℝ) ≤ ((65 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-21749192093/2500000000000 : ℚ) : ℝ)
      = ((310087/2500000 : ℚ) : ℝ) * ((-70139/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c66 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((369999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -297947/1000000) (δ := 11417/1000000000) (ψ := -35361/50000) 226 151
    (log_br_66).1 (log_br_66).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t66 : ((227687701693/5000000000000 : ℚ) : ℝ) ≤ stT226 66 := by
  have hc : ((369949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((66 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c66).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_66).1
  have hw2 : ((66 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((615457/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((227687701693/5000000000000 : ℚ) : ℝ)
      = ((615457/5000000 : ℚ) : ℝ) * ((369949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c67 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-593967/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 344809/625000) (δ := 5693/500000000) (ψ := -35361/50000) 226 151
    (log_br_67).1 (log_br_67).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t67 : ((-145141519763/2000000000000 : ℚ) : ℝ) ≤ stT226 67 := by
  have hc : ((-594017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((67 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c67).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_67).2
  have h0 : (0:ℝ) ≤ ((67 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-145141519763/2000000000000 : ℚ) : ℝ)
      = ((244339/2000000 : ℚ) : ℝ) * ((-594017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c68 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((746377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -227561/1250000) (δ := 1131/100000000) (ψ := -35361/50000) 226 152
    (log_br_68).1 (log_br_68).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t68 : ((452527166853/5000000000000 : ℚ) : ℝ) ≤ stT226 68 := by
  have hc : ((746327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((68 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c68).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_68).1
  have hw2 : ((68 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((606339/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((452527166853/5000000000000 : ℚ) : ℝ)
      = ((606339/5000000 : ℚ) : ℝ) * ((746327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c69 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-841653/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3213917/5000000) (δ := 1131/100000000) (ψ := -35361/50000) 226 152
    (log_br_69).1 (log_br_69).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t69 : ((-1013291731877/10000000000000 : ℚ) : ℝ) ≤ stT226 69 := by
  have hc : ((-841703/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((69 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c69).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_69).2
  have h0 : (0:ℝ) ≤ ((69 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1013291731877/10000000000000 : ℚ) : ℝ)
      = ((1203859/10000000 : ℚ) : ℝ) * ((-841703/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c70 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((895961/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -575257/5000000) (δ := 11403/1000000000) (ψ := -35361/50000) 226 153
    (log_br_70).1 (log_br_70).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t70 : ((267704478177/2500000000000 : ℚ) : ℝ) ≤ stT226 70 := by
  have hc : ((895911/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((70 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c70).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_70).1
  have hw2 : ((70 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((298807/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((267704478177/2500000000000 : ℚ) : ℝ)
      = ((298807/2500000 : ℚ) : ℝ) * ((895911/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c71 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-922581/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1372757/2000000) (δ := 11403/1000000000) (ψ := -35361/50000) 226 153
    (log_br_71).1 (log_br_71).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t71 : ((-547480931721/5000000000000 : ℚ) : ℝ) ≤ stT226 71 := by
  have hc : ((-922631/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((71 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c71).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_71).2
  have h0 : (0:ℝ) ≤ ((71 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-547480931721/5000000000000 : ℚ) : ℝ)
      = ((593391/5000000 : ℚ) : ℝ) * ((-922631/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c72 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((929859/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -941919/10000000) (δ := 1437/125000000) (ψ := -35361/50000) 226 154
    (log_br_72).1 (log_br_72).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t72 : ((1095790134399/10000000000000 : ℚ) : ℝ) ≤ stT226 72 := by
  have hc : ((929809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((72 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c72).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_72).1
  have hw2 : ((72 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1178511/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1095790134399/10000000000000 : ℚ) : ℝ)
      = ((1178511/10000000 : ℚ) : ℝ) * ((929809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c73 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-460321/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 214103/312500) (δ := 11307/1000000000) (ψ := -35361/50000) 226 154
    (log_br_73).1 (log_br_73).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t73 : ((-67349310319/625000000000 : ℚ) : ℝ) ≤ stT226 73 := by
  have hc : ((-230173/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((73 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c73).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_73).2
  have h0 : (0:ℝ) ≤ ((73 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-67349310319/625000000000 : ℚ) : ℝ)
      = ((292603/2500000 : ℚ) : ℝ) * ((-230173/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c74 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((446281/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1169503/10000000) (δ := 5707/500000000) (ψ := -35361/50000) 226 155
    (log_br_74).1 (log_br_74).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t74 : ((8105654529/78125000000 : ℚ) : ℝ) ≤ stT226 74 := by
  have hc : ((27891/31250 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((74 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c74).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_74).1
  have hw2 : ((74 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((290619/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8105654529/78125000000 : ℚ) : ℝ)
      = ((290619/2500000 : ℚ) : ℝ) * ((27891/31250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c75 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-838771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1603637/2500000) (δ := 11389/1000000000) (ψ := -35361/50000) 226 155
    (log_br_75).1 (log_br_75).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t75 : ((-968587447521/10000000000000 : ℚ) : ℝ) ≤ stT226 75 := by
  have hc : ((-838821/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((75 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c75).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_75).2
  have h0 : (0:ℝ) ≤ ((75 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-968587447521/10000000000000 : ℚ) : ℝ)
      = ((1154701/10000000 : ℚ) : ℝ) * ((-838821/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c76 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((149839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1809877/10000000) (δ := 5661/500000000) (ψ := -35361/50000) 226 156
    (log_br_76).1 (log_br_76).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t76 : ((85932774831/1000000000000 : ℚ) : ℝ) ≤ stT226 76 := by
  have hc : ((149829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((76 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c76).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_76).1
  have hw2 : ((76 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((573539/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((85932774831/1000000000000 : ℚ) : ℝ)
      = ((573539/5000000 : ℚ) : ℝ) * ((149829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c77 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-612759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5575859/10000000) (δ := 11481/1000000000) (ψ := -35361/50000) 226 156
    (log_br_77).1 (log_br_77).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t77 : ((-349180406627/5000000000000 : ℚ) : ℝ) ≤ stT226 77 := by
  have hc : ((-612809/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((77 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c77).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_77).2
  have h0 : (0:ℝ) ≤ ((77 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-349180406627/5000000000000 : ℚ) : ℝ)
      = ((569803/5000000 : ℚ) : ℝ) * ((-612809/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c78 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((84123/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2841683/10000000) (δ := 5687/500000000) (ψ := -35361/50000) 226 157
    (log_br_78).1 (log_br_78).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t78 : ((95239215301/2000000000000 : ℚ) : ℝ) ≤ stT226 78 := by
  have hc : ((84113/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((78 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c78).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_78).1
  have hw2 : ((78 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1132277/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((95239215301/2000000000000 : ℚ) : ℝ)
      = ((1132277/10000000 : ℚ) : ℝ) * ((84113/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c79 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-10669/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1088963/2500000) (δ := 5687/500000000) (ψ := -35361/50000) 226 157
    (log_br_79).1 (log_br_79).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t79 : ((-3001769943/156250000000 : ℚ) : ℝ) ≤ stT226 79 := by
  have hc : ((-85377/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((79 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c79).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_79).2
  have h0 : (0:ℝ) ≤ ((79 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-3001769943/156250000000 : ℚ) : ℝ)
      = ((35159/312500 : ℚ) : ℝ) * ((-85377/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c80 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-7931/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4245089/10000000) (δ := 1417/125000000) (ψ := -35361/50000) 226 158
    (log_br_80).1 (log_br_80).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t80 : ((-35482486041/2500000000000 : ℚ) : ℝ) ≤ stT226 80 := by
  have hc : ((-63473/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((80 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c80).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_80).2
  have h0 : (0:ℝ) ≤ ((80 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35482486041/2500000000000 : ℚ) : ℝ)
      = ((559017/5000000 : ℚ) : ℝ) * ((-63473/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c81 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((89031/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2773623/10000000) (δ := 11467/1000000000) (ψ := -35361/50000) 226 158
    (log_br_81).1 (log_br_81).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t81 : ((98912212331/2000000000000 : ℚ) : ℝ) ≤ stT226 81 := by
  have hc : ((89021/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((81 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c81).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_81).1
  have hw2 : ((81 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1111111/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((98912212331/2000000000000 : ℚ) : ℝ)
      = ((1111111/10000000 : ℚ) : ℝ) * ((89021/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c82 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-368931/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6001733/10000000) (δ := 11443/1000000000) (ψ := -35361/50000) 226 159
    (log_br_82).1 (log_br_82).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t82 : ((-25465250881/312500000000 : ℚ) : ℝ) ≤ stT226 82 := by
  have hc : ((-92239/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((82 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c82).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_82).2
  have h0 : (0:ℝ) ≤ ((82 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-25465250881/312500000000 : ℚ) : ℝ)
      = ((276079/2500000 : ℚ) : ℝ) * ((-92239/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c83 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((943173/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 423429/5000000) (δ := 11443/1000000000) (ψ := -35361/50000) 226 159
    (log_br_83).1 (log_br_83).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t83 : ((517605707983/5000000000000 : ℚ) : ℝ) ≤ stT226 83 := by
  have hc : ((943123/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((83 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c83).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_83).1
  have hw2 : ((83 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((548821/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((517605707983/5000000000000 : ℚ) : ℝ)
      = ((548821/5000000 : ℚ) : ℝ) * ((943123/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c84 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-995373/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3806691/5000000) (δ := 569/25000000) (ψ := -35361/50000) 226 159
    (log_br_84).1 (log_br_84).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t84 : ((-108609608107/1000000000000 : ℚ) : ℝ) ≤ stT226 84 := by
  have hc : ((-995423/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((84 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c84).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_84).2
  have h0 : (0:ℝ) ≤ ((84 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-108609608107/1000000000000 : ℚ) : ℝ)
      = ((109109/1000000 : ℚ) : ℝ) * ((-995423/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c85 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((422763/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1408117/10000000) (δ := 11453/1000000000) (ψ := -35361/50000) 226 160
    (log_br_85).1 (log_br_85).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t85 : ((57315452147/625000000000 : ℚ) : ℝ) ≤ stT226 85 := by
  have hc : ((211369/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((85 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c85).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_85).1
  have hw2 : ((85 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((271163/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((57315452147/625000000000 : ℚ) : ℝ)
      = ((271163/2500000 : ℚ) : ℝ) * ((211369/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c86 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-19501/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5200123/10000000) (δ := 11453/1000000000) (ψ := -35361/50000) 226 160
    (log_br_86).1 (log_br_86).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t86 : ((-2628828873/50000000000 : ℚ) : ℝ) ≤ stT226 86 := by
  have hc : ((-19503/40000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((86 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c86).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_86).2
  have h0 : (0:ℝ) ≤ ((86 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2628828873/50000000000 : ℚ) : ℝ)
      = ((134791/1250000 : ℚ) : ℝ) * ((-19503/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c87 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-783/40000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3975931/10000000) (δ := 11457/1000000000) (ψ := -35361/50000) 226 161
    (log_br_87).1 (log_br_87).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t87 : ((-168321741/80000000000 : ℚ) : ℝ) ≤ stT226 87 := by
  have hc : ((-157/8000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((87 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c87).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_87).2
  have h0 : (0:ℝ) ≤ ((87 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-168321741/80000000000 : ℚ) : ℝ)
      = ((1072113/10000000 : ℚ) : ℝ) * ((-157/8000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c88 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((546587/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 620321/2500000) (δ := 5673/500000000) (ψ := -35361/50000) 226 161
    (log_br_88).1 (log_br_88).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t88 : ((582610081611/10000000000000 : ℚ) : ℝ) ≤ stT226 88 := by
  have hc : ((546537/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((88 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c88).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_88).1
  have hw2 : ((88 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1066003/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((582610081611/10000000000000 : ℚ) : ℝ)
      = ((1066003/10000000 : ℚ) : ℝ) * ((546537/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c89 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-919257/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3421231/5000000) (δ := 5719/500000000) (ψ := -35361/50000) 226 162
    (log_br_89).1 (log_br_89).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t89 : ((-487231790693/5000000000000 : ℚ) : ℝ) ≤ stT226 89 := by
  have hc : ((-919307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((89 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c89).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_89).2
  have h0 : (0:ℝ) ≤ ((89 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-487231790693/5000000000000 : ℚ) : ℝ)
      = ((529999/5000000 : ℚ) : ℝ) * ((-919307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c90 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((19553/20000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -529547/10000000) (δ := 2273/200000000) (ψ := -35361/50000) 226 162
    (log_br_90).1 (log_br_90).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t90 : ((161012553/1562500000 : ℚ) : ℝ) ≤ stT226 90 := by
  have hc : ((611/625 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((90 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c90).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_90).1
  have hw2 : ((90 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((263523/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161012553/1562500000 : ℚ) : ℝ)
      = ((263523/2500000 : ℚ) : ℝ) * ((611/625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c91 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-327677/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2856809/5000000) (δ := 11319/500000000) (ψ := -35361/50000) 226 162
    (log_br_91).1 (log_br_91).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t91 : ((-34352509107/500000000000 : ℚ) : ℝ) ≤ stT226 91 := by
  have hc : ((-163851/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((91 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c91).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_91).2
  have h0 : (0:ℝ) ≤ ((91 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-34352509107/500000000000 : ℚ) : ℝ)
      = ((209657/2000000 : ℚ) : ℝ) * ((-163851/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c92 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((4301/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -477429/1250000) (δ := 11331/1000000000) (ψ := -35361/50000) 226 163
    (log_br_92).1 (log_br_92).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t92 : ((139965291/31250000000 : ℚ) : ℝ) ≤ stT226 92 := by
  have hc : ((537/12500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((92 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c92).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_92).1
  have hw2 : ((92 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((260643/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((139965291/31250000000 : ℚ) : ℝ)
      = ((260643/2500000 : ℚ) : ℝ) * ((537/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c93 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((304701/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2288727/10000000) (δ := 717/62500000) (ψ := -35361/50000) 226 163
    (log_br_93).1 (log_br_93).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t93 : ((78983520719/1250000000000 : ℚ) : ℝ) ≤ stT226 93 := by
  have hc : ((76169/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((93 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c93).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_93).1
  have hw2 : ((93 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1036951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((78983520719/1250000000000 : ℚ) : ℝ)
      = ((1036951/10000000 : ℚ) : ℝ) * ((76169/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c94 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-61363/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -922049/1250000) (δ := 11379/1000000000) (ψ := -35361/50000) 226 164
    (log_br_94).1 (log_br_94).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t94 : ((-253177485519/2500000000000 : ℚ) : ℝ) ≤ stT226 94 := by
  have hc : ((-490929/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((94 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c94).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_94).2
  have h0 : (0:ℝ) ≤ ((94 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-253177485519/2500000000000 : ℚ) : ℝ)
      = ((515711/5000000 : ℚ) : ℝ) * ((-490929/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c95 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((169557/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -698753/5000000) (δ := 357/31250000) (ψ := -35361/50000) 226 164
    (log_br_95).1 (log_br_95).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t95 : ((86975745983/1000000000000 : ℚ) : ℝ) ≤ stT226 95 := by
  have hc : ((169547/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((95 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c95).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_95).1
  have hw2 : ((95 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((512989/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((86975745983/1000000000000 : ℚ) : ℝ)
      = ((512989/5000000 : ℚ) : ℝ) * ((169547/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c96 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-234511/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4518779/10000000) (δ := 11379/1000000000) (ψ := -35361/50000) 226 164
    (log_br_96).1 (log_br_96).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t96 : ((-239397882381/10000000000000 : ℚ) : ℝ) ≤ stT226 96 := by
  have hc : ((-234561/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((96 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c96).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_96).2
  have h0 : (0:ℝ) ≤ ((96 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-239397882381/10000000000000 : ℚ) : ℝ)
      = ((1020621/10000000 : ℚ) : ℝ) * ((-234561/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c97 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-133407/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2667101/5000000) (δ := 5743/500000000) (ψ := -35361/50000) 226 165
    (log_br_97).1 (log_br_97).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t97 : ((-270934178133/5000000000000 : ℚ) : ℝ) ≤ stT226 97 := by
  have hc : ((-266839/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((97 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c97).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_97).2
  have h0 : (0:ℝ) ≤ ((97 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-270934178133/5000000000000 : ℚ) : ℝ)
      = ((1015347/10000000 : ℚ) : ℝ) * ((-266839/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c98 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((983067/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5759/125000) (δ := 11317/1000000000) (ψ := -35361/50000) 226 165
    (log_br_98).1 (log_br_98).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t98 : ((124124573573/1250000000000 : ℚ) : ℝ) ≤ stT226 98 := by
  have hc : ((983017/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((98 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c98).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_98).1
  have hw2 : ((98 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((126269/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((124124573573/1250000000000 : ℚ) : ℝ)
      = ((126269/1250000 : ℚ) : ℝ) * ((983017/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c99 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-394117/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3098413/5000000) (δ := 11317/1000000000) (ψ := -35361/50000) 226 165
    (log_br_99).1 (log_br_99).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t99 : ((-99031921849/1250000000000 : ℚ) : ℝ) ≤ stT226 99 := by
  have hc : ((-197071/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((99 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c99).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_99).2
  have h0 : (0:ℝ) ≤ ((99 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-99031921849/1250000000000 : ℚ) : ℝ)
      = ((502519/5000000 : ℚ) : ℝ) * ((-197071/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c100 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((377/10000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1916359/5000000) (δ := 1141/100000000) (ψ := -35361/50000) 226 166
    (log_br_100).1 (log_br_100).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t100 : ((752999247/200000000000 : ℚ) : ℝ) ≤ stT226 100 := by
  have hc : ((753/20000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((100 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c100).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_100).1
  have hw2 : ((100 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((999999/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((752999247/200000000000 : ℚ) : ℝ)
      = ((999999/10000000 : ℚ) : ℝ) * ((753/20000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c101 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((94329/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 894629/5000000) (δ := 1141/100000000) (ψ := -35361/50000) 226 166
    (log_br_101).1 (log_br_101).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t101 : ((375418504767/5000000000000 : ℚ) : ℝ) ≤ stT226 101 := by
  have hc : ((377291/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((101 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c101).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_101).1
  have hw2 : ((101 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((995037/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((375418504767/5000000000000 : ℚ) : ℝ)
      = ((995037/10000000 : ℚ) : ℝ) * ((377291/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c102 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-980211/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 229869/312500) (δ := 11393/1000000000) (ψ := -35361/50000) 226 166
    (log_br_102).1 (log_br_102).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t102 : ((-242650867157/2500000000000 : ℚ) : ℝ) ≤ stT226 102 := by
  have hc : ((-980261/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((102 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c102).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_102).2
  have h0 : (0:ℝ) ≤ ((102 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-242650867157/2500000000000 : ℚ) : ℝ)
      = ((247537/2500000 : ℚ) : ℝ) * ((-980261/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c103 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((421241/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2839959/10000000) (δ := 11303/1000000000) (ψ := -35361/50000) 226 167
    (log_br_103).1 (log_br_103).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t103 : ((415011706839/10000000000000 : ℚ) : ℝ) ≤ stT226 103 := by
  have hc : ((421191/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((103 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c103).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_103).1
  have hw2 : ((103 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((985329/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((415011706839/10000000000000 : ℚ) : ℝ)
      = ((985329/10000000 : ℚ) : ℝ) * ((421191/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c104 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((249823/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 523803/2000000) (δ := 23/2000000) (ψ := -35361/50000) 226 167
    (log_br_104).1 (log_br_104).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t104 : ((6123673071/125000000000 : ℚ) : ℝ) ≤ stT226 104 := by
  have hc : ((124899/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((104 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c104).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_104).1
  have hw2 : ((104 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((49029/500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6123673071/125000000000 : ℚ) : ℝ)
      = ((49029/500000 : ℚ) : ℝ) * ((124899/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c105 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-24941/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7682181/10000000) (δ := 713/62500000) (ψ := -35361/50000) 226 168
    (log_br_105).1 (log_br_105).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t105 : ((-97364666869/1000000000000 : ℚ) : ℝ) ≤ stT226 105 := by
  have hc : ((-99769/100000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((105 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c105).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_105).2
  have h0 : (0:ℝ) ≤ ((105 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-97364666869/1000000000000 : ℚ) : ℝ)
      = ((975901/10000000 : ℚ) : ℝ) * ((-99769/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c106 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((149321/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -581679/2500000) (δ := 2279/200000000) (ψ := -35361/50000) 226 168
    (log_br_106).1 (log_br_106).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t106 : ((58008442569/1000000000000 : ℚ) : ℝ) ≤ stT226 106 := by
  have hc : ((298617/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((106 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c106).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_106).1
  have hw2 : ((106 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((194257/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((58008442569/1000000000000 : ℚ) : ℝ)
      = ((194257/2000000 : ℚ) : ℝ) * ((298617/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c107 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((23147/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2978521/10000000) (δ := 2279/200000000) (ψ := -35361/50000) 226 168
    (log_br_107).1 (log_br_107).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t107 : ((11187008571/312500000000 : ℚ) : ℝ) ≤ stT226 107 := by
  have hc : ((185151/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((107 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c107).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_107).1
  have hw2 : ((107 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((60421/625000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11187008571/312500000000 : ℚ) : ℝ)
      = ((60421/625000 : ℚ) : ℝ) * ((185151/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c108 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-494223/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3736793/5000000) (δ := 2263/200000000) (ψ := -35361/50000) 226 169
    (log_br_108).1 (log_br_108).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t108 : ((-59448829031/625000000000 : ℚ) : ℝ) ≤ stT226 108 := by
  have hc : ((-61781/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((108 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c108).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_108).2
  have h0 : (0:ℝ) ≤ ((108 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-59448829031/625000000000 : ℚ) : ℝ)
      = ((962251/10000000 : ℚ) : ℝ) * ((-61781/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c109 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((616519/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2266207/10000000) (δ := 2263/200000000) (ψ := -35361/50000) 226 169
    (log_br_109).1 (log_br_109).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t109 : ((295235018197/5000000000000 : ℚ) : ℝ) ≤ stT226 109 := by
  have hc : ((616469/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((109 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c109).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_109).1
  have hw2 : ((109 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((478913/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((295235018197/5000000000000 : ℚ) : ℝ)
      = ((478913/5000000 : ℚ) : ℝ) * ((616469/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c110 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((80333/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 578731/2000000) (δ := 359/31250000) (ψ := -35361/50000) 226 169
    (log_br_110).1 (log_br_110).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t110 : ((38292464113/1000000000000 : ℚ) : ℝ) ≤ stT226 110 := by
  have hc : ((80323/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((110 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c110).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_110).1
  have hw2 : ((110 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((476731/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38292464113/1000000000000 : ℚ) : ℝ)
      = ((476731/5000000 : ℚ) : ℝ) * ((80323/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c111 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-998131/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3850557/5000000) (δ := 5711/500000000) (ψ := -35361/50000) 226 170
    (log_br_111).1 (log_br_111).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t111 : ((-473715740799/5000000000000 : ℚ) : ℝ) ≤ stT226 111 := by
  have hc : ((-998181/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((111 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c111).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_111).2
  have h0 : (0:ℝ) ≤ ((111 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-473715740799/5000000000000 : ℚ) : ℝ)
      = ((474579/5000000 : ℚ) : ℝ) * ((-998181/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c112 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((15453/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -526771/2000000) (δ := 5711/500000000) (ψ := -35361/50000) 226 170
    (log_br_112).1 (log_br_112).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t112 : ((233603732153/5000000000000 : ℚ) : ℝ) ≤ stT226 112 := by
  have hc : ((247223/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((112 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c112).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_112).1
  have hw2 : ((112 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((944911/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((233603732153/5000000000000 : ℚ) : ℝ)
      = ((944911/10000000 : ℚ) : ℝ) * ((247223/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c113 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((115461/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 238843/1000000) (δ := 5711/500000000) (ψ := -35361/50000) 226 170
    (log_br_113).1 (log_br_113).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t113 : ((1357588309/25000000000 : ℚ) : ℝ) ≤ stT226 113 := by
  have hc : ((115451/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((113 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c113).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_113).1
  have hw2 : ((113 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((11759/125000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1357588309/25000000000 : ℚ) : ℝ)
      = ((11759/125000 : ℚ) : ℝ) * ((115451/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c114 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-981043/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7366419/10000000) (δ := 5711/500000000) (ψ := -35361/50000) 226 170
    (log_br_114).1 (log_br_114).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t114 : ((-459438984249/5000000000000 : ℚ) : ℝ) ≤ stT226 114 := by
  have hc : ((-981093/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((114 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c114).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_114).2
  have h0 : (0:ℝ) ≤ ((114 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-459438984249/5000000000000 : ℚ) : ℝ)
      = ((468293/5000000 : ℚ) : ℝ) * ((-981093/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c115 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((103249/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -851751/2500000) (δ := 11329/1000000000) (ψ := -35361/50000) 226 171
    (log_br_115).1 (log_br_115).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t115 : ((1504012389/78125000000 : ℚ) : ℝ) ≤ stT226 115 := by
  have hc : ((12903/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((115 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c115).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_115).1
  have hw2 : ((115 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((116563/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((1504012389/78125000000 : ℚ) : ℝ)
      = ((116563/1250000 : ℚ) : ℝ) * ((12903/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c116 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((828761/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 742383/5000000) (δ := 11329/1000000000) (ψ := -35361/50000) 226 171
    (log_br_116).1 (log_br_116).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t116 : ((192359568609/2500000000000 : ℚ) : ℝ) ≤ stT226 116 := by
  have hc : ((828711/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((116 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c116).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_116).1
  have hw2 : ((116 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((232119/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((192359568609/2500000000000 : ℚ) : ℝ)
      = ((232119/2500000 : ℚ) : ℝ) * ((828711/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c117 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-102617/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6334613/10000000) (δ := 11329/1000000000) (ψ := -35361/50000) 226 171
    (log_br_117).1 (log_br_117).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t117 : ((-379501188993/5000000000000 : ℚ) : ℝ) ≤ stT226 117 := by
  have hc : ((-410493/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((117 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c117).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_117).2
  have h0 : (0:ℝ) ≤ ((117 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-379501188993/5000000000000 : ℚ) : ℝ)
      = ((924501/10000000 : ℚ) : ℝ) * ((-410493/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c118 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-252367/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -912961/2000000) (δ := 11367/1000000000) (ψ := -35361/50000) 226 172
    (log_br_118).1 (log_br_118).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t118 : ((-9294751191/400000000000 : ℚ) : ℝ) ≤ stT226 118 := by
  have hc : ((-252417/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((118 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c118).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_118).2
  have h0 : (0:ℝ) ≤ ((118 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-9294751191/400000000000 : ℚ) : ℝ)
      = ((36823/400000 : ℚ) : ℝ) * ((-252417/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c119 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((996701/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 203117/10000000) (δ := 11367/1000000000) (ψ := -35361/50000) 226 172
    (log_br_119).1 (log_br_119).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t119 : ((456813989199/5000000000000 : ℚ) : ℝ) ≤ stT226 119 := by
  have hc : ((996651/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((119 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c119).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_119).1
  have hw2 : ((119 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((458349/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((456813989199/5000000000000 : ℚ) : ℝ)
      = ((458349/5000000 : ℚ) : ℝ) * ((996651/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c120 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-390971/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4931207/10000000) (δ := 2859/250000000) (ψ := -35361/50000) 226 172
    (log_br_120).1 (log_br_120).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t120 : ((-356951731291/10000000000000 : ℚ) : ℝ) ≤ stT226 120 := by
  have hc : ((-391021/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((120 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c120).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_120).2
  have h0 : (0:ℝ) ≤ ((120 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-356951731291/10000000000000 : ℚ) : ℝ)
      = ((912871/10000000 : ℚ) : ℝ) * ((-391021/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c121 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-760691/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1217587/2000000) (δ := 11459/1000000000) (ψ := -35361/50000) 226 173
    (log_br_121).1 (log_br_121).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t121 : ((-691582796431/10000000000000 : ℚ) : ℝ) ≤ stT226 121 := by
  have hc : ((-760741/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((121 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c121).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_121).2
  have h0 : (0:ℝ) ≤ ((121 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-691582796431/10000000000000 : ℚ) : ℝ)
      = ((909091/10000000 : ℚ) : ℝ) * ((-760741/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c122 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((209787/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -718851/5000000) (δ := 709/62500000) (ψ := -35361/50000) 226 173
    (log_br_122).1 (log_br_122).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t122 : ((379841623993/5000000000000 : ℚ) : ℝ) ≤ stT226 122 := by
  have hc : ((419549/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((122 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c122).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_122).1
  have hw2 : ((122 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((905357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((379841623993/5000000000000 : ℚ) : ℝ)
      = ((905357/10000000 : ℚ) : ℝ) * ((419549/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c123 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((4632/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1587281/5000000) (δ := 11459/1000000000) (ψ := -35361/50000) 226 173
    (log_br_123).1 (log_br_123).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t123 : ((133626444131/5000000000000 : ℚ) : ℝ) ≤ stT226 123 := by
  have hc : ((148199/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((123 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c123).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_123).1
  have hw2 : ((123 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((901669/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((133626444131/5000000000000 : ℚ) : ℝ)
      = ((901669/10000000 : ℚ) : ℝ) * ((148199/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c124 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-499563/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 193737/250000) (δ := 11459/1000000000) (ψ := -35361/50000) 226 173
    (log_br_124).1 (log_br_124).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t124 : ((-112160878219/1250000000000 : ℚ) : ℝ) ≤ stT226 124 := by
  have hc : ((-124897/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((124 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c124).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_124).2
  have h0 : (0:ℝ) ≤ ((124 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-112160878219/1250000000000 : ℚ) : ℝ)
      = ((898027/10000000 : ℚ) : ℝ) * ((-124897/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c125 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((12581/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -342029/1000000) (δ := 1419/125000000) (ψ := -35361/50000) 226 174
    (log_br_125).1 (log_br_125).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t125 : ((89999928021/5000000000000 : ℚ) : ℝ) ≤ stT226 125 := by
  have hc : ((100623/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((125 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c125).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_125).1
  have hw2 : ((125 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((894427/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((89999928021/5000000000000 : ℚ) : ℝ)
      = ((894427/10000000 : ℚ) : ℝ) * ((100623/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c126 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((453919/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1081743/10000000) (δ := 1419/125000000) (ψ := -35361/50000) 226 174
    (log_br_126).1 (log_br_126).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t126 : ((20218027389/250000000000 : ℚ) : ℝ) ≤ stT226 126 := by
  have hc : ((226947/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((126 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c126).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_126).1
  have hw2 : ((126 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((89087/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((20218027389/250000000000 : ℚ) : ℝ)
      = ((89087/1000000 : ℚ) : ℝ) * ((226947/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c127 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-120791/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 8877/16000) (δ := 11451/1000000000) (ψ := -35361/50000) 226 174
    (log_br_127).1 (log_br_127).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t127 : ((-107193612957/2000000000000 : ℚ) : ℝ) ≤ stT226 127 := by
  have hc : ((-120801/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((127 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c127).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_127).2
  have h0 : (0:ℝ) ≤ ((127 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-107193612957/2000000000000 : ℚ) : ℝ)
      = ((887357/10000000 : ℚ) : ℝ) * ((-120801/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c128 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-329909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5728431/10000000) (δ := 2289/200000000) (ψ := -35361/50000) 226 175
    (log_br_128).1 (log_br_128).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t128 : ((-36452922957/625000000000 : ℚ) : ℝ) ≤ stT226 128 := by
  have hc : ((-164967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((128 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c128).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_128).2
  have h0 : (0:ℝ) ≤ ((128 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-36452922957/625000000000 : ℚ) : ℝ)
      = ((220971/2500000 : ℚ) : ℝ) * ((-164967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c129 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((215373/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -41609/312500) (δ := 2289/200000000) (ψ := -35361/50000) 226 175
    (log_br_129).1 (log_br_129).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t129 : ((7584566089/100000000000 : ℚ) : ℝ) ≤ stT226 129 := by
  have hc : ((430721/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((129 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c129).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_129).1
  have hw2 : ((129 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((17609/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7584566089/100000000000 : ℚ) : ℝ)
      = ((17609/200000 : ℚ) : ℝ) * ((430721/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c130 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((350607/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1515721/5000000) (δ := 2289/200000000) (ψ := -35361/50000) 226 175
    (log_br_130).1 (log_br_130).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t130 : ((153729410653/5000000000000 : ℚ) : ℝ) ≤ stT226 130 := by
  have hc : ((350557/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((130 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c130).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_130).1
  have hw2 : ((130 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((438529/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((153729410653/5000000000000 : ℚ) : ℝ)
      = ((438529/5000000 : ℚ) : ℝ) * ((350557/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c131 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-980619/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7360981/10000000) (δ := 5679/500000000) (ψ := -35361/50000) 226 175
    (log_br_131).1 (log_br_131).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t131 : ((-171363081729/2000000000000 : ℚ) : ℝ) ≤ stT226 131 := by
  have hc : ((-980669/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((131 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c131).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_131).2
  have h0 : (0:ℝ) ≤ ((131 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-171363081729/2000000000000 : ℚ) : ℝ)
      = ((174741/2000000 : ℚ) : ℝ) * ((-980669/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c132 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-49337/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4050383/10000000) (δ := 2293/200000000) (ψ := -35361/50000) 226 176
    (log_br_132).1 (log_br_132).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t132 : ((-42985901543/10000000000000 : ℚ) : ℝ) ≤ stT226 132 := by
  have hc : ((-49387/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((132 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c132).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_132).2
  have h0 : (0:ℝ) ≤ ((132 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-42985901543/10000000000000 : ℚ) : ℝ)
      = ((870389/10000000 : ℚ) : ℝ) * ((-49387/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c133 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((498173/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 42757/2000000) (δ := 2293/200000000) (ψ := -35361/50000) 226 176
    (log_br_133).1 (log_br_133).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t133 : ((107987153533/1250000000000 : ℚ) : ℝ) ≤ stT226 133 := by
  have hc : ((124537/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((133 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c133).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_133).1
  have hw2 : ((133 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((867109/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((107987153533/1250000000000 : ℚ) : ℝ)
      = ((867109/10000000 : ℚ) : ℝ) * ((124537/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c134 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-51529/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2223001/5000000) (δ := 4533/200000000) (ψ := -35361/50000) 226 176
    (log_br_134).1 (log_br_134).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t134 : ((-89050208127/5000000000000 : ℚ) : ℝ) ≤ stT226 134 := by
  have hc : ((-103083/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((134 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c134).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_134).2
  have h0 : (0:ℝ) ≤ ((134 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-89050208127/5000000000000 : ℚ) : ℝ)
      = ((863869/10000000 : ℚ) : ℝ) * ((-103083/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c135 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-475071/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1412243/2000000) (δ := 11431/1000000000) (ψ := -35361/50000) 226 177
    (log_br_135).1 (log_br_135).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t135 : ((-51112193581/625000000000 : ℚ) : ℝ) ≤ stT226 135 := by
  have hc : ((-59387/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((135 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c135).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_135).2
  have h0 : (0:ℝ) ≤ ((135 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-51112193581/625000000000 : ℚ) : ℝ)
      = ((860663/10000000 : ℚ) : ℝ) * ((-59387/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c136 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((40247/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1445729/5000000) (δ := 2843/250000000) (ψ := -35361/50000) 226 177
    (log_br_136).1 (log_br_136).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t136 : ((4313399133/125000000000 : ℚ) : ℝ) ≤ stT226 136 := by
  have hc : ((20121/50000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((136 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c136).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_136).1
  have hw2 : ((136 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((214373/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4313399133/125000000000 : ℚ) : ℝ)
      = ((214373/2500000 : ℚ) : ℝ) * ((20121/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c137 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((439003/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 311947/2500000) (δ := 11431/1000000000) (ψ := -35361/50000) 226 177
    (log_br_137).1 (log_br_137).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t137 : ((187521963573/2500000000000 : ℚ) : ℝ) ≤ stT226 137 := by
  have hc : ((219489/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((137 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c137).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_137).1
  have hw2 : ((137 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((854357/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((187521963573/2500000000000 : ℚ) : ℝ)
      = ((854357/10000000 : ℚ) : ℝ) * ((219489/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c138 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-67659/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 83701/156250) (δ := 2843/250000000) (ψ := -35361/50000) 226 177
    (log_br_138).1 (log_br_138).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t138 : ((-230402070877/5000000000000 : ℚ) : ℝ) ≤ stT226 138 := by
  have hc : ((-270661/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((138 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c138).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_138).2
  have h0 : (0:ℝ) ≤ ((138 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-230402070877/5000000000000 : ℚ) : ℝ)
      = ((851257/10000000 : ℚ) : ℝ) * ((-270661/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c139 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-201573/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -627163/1000000) (δ := 2831/250000000) (ψ := -35361/50000) 226 178
    (log_br_139).1 (log_br_139).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t139 : ((-341965207319/5000000000000 : ℚ) : ℝ) ≤ stT226 139 := by
  have hc : ((-403171/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((139 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c139).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_139).2
  have h0 : (0:ℝ) ≤ ((139 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-341965207319/5000000000000 : ℚ) : ℝ)
      = ((848189/10000000 : ℚ) : ℝ) * ((-403171/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c140 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((315261/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2221427/10000000) (δ := 11479/1000000000) (ψ := -35361/50000) 226 178
    (log_br_140).1 (log_br_140).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t140 : ((33302870793/625000000000 : ℚ) : ℝ) ≤ stT226 140 := by
  have hc : ((78809/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((140 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c140).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_140).1
  have hw2 : ((140 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((422577/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33302870793/625000000000 : ℚ) : ℝ)
      = ((422577/5000000 : ℚ) : ℝ) * ((78809/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c141 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((751831/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 56247/312500) (δ := 11479/1000000000) (ψ := -35361/50000) 226 178
    (log_br_141).1 (log_br_141).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t141 : ((633113120931/10000000000000 : ℚ) : ℝ) ≤ stT226 141 := by
  have hc : ((751781/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((141 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c141).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_141).1
  have hw2 : ((141 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((842151/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((633113120931/10000000000000 : ℚ) : ℝ)
      = ((842151/10000000 : ℚ) : ℝ) * ((751781/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c142 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-135793/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 724109/1250000) (δ := 11479/1000000000) (ψ := -35361/50000) 226 178
    (log_br_142).1 (log_br_142).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t142 : ((-56981716573/1000000000000 : ℚ) : ℝ) ≤ stT226 142 := by
  have hc : ((-135803/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((142 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c142).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_142).2
  have h0 : (0:ℝ) ≤ ((142 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-56981716573/1000000000000 : ℚ) : ℝ)
      = ((419591/5000000 : ℚ) : ℝ) * ((-135803/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c143 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-723779/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1487537/2500000) (δ := 1427/125000000) (ψ := -35361/50000) 226 179
    (log_br_143).1 (log_br_143).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t143 : ((-605296934447/10000000000000 : ℚ) : ℝ) ≤ stT226 143 := by
  have hc : ((-723829/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((143 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c143).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_143).2
  have h0 : (0:ℝ) ≤ ((143 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-605296934447/10000000000000 : ℚ) : ℝ)
      = ((836243/10000000 : ℚ) : ℝ) * ((-723829/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c144 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((692999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2012889/10000000) (δ := 1427/125000000) (ψ := -35361/50000) 226 179
    (log_br_144).1 (log_br_144).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t144 : ((577457269017/10000000000000 : ℚ) : ℝ) ≤ stT226 144 := by
  have hc : ((692949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((144 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c144).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_144).1
  have hw2 : ((144 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((833333/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((577457269017/10000000000000 : ℚ) : ℝ)
      = ((833333/10000000 : ℚ) : ℝ) * ((692949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c145 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((725609/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 948597/5000000) (δ := 11387/1000000000) (ψ := -35361/50000) 226 179
    (log_br_145).1 (log_br_145).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t145 : ((301271686893/5000000000000 : ℚ) : ℝ) ≤ stT226 145 := by
  have hc : ((725559/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((145 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c145).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_145).1
  have hw2 : ((145 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((415227/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((301271686893/5000000000000 : ℚ) : ℝ)
      = ((415227/5000000 : ℚ) : ℝ) * ((725559/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c146 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-675289/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2890191/5000000) (δ := 1427/125000000) (ψ := -35361/50000) 226 179
    (log_br_146).1 (log_br_146).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t146 : ((-279457304217/5000000000000 : ℚ) : ℝ) ≤ stT226 146 := by
  have hc : ((-675339/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((146 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c146).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_146).2
  have h0 : (0:ℝ) ≤ ((146 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-279457304217/5000000000000 : ℚ) : ℝ)
      = ((413803/5000000 : ℚ) : ℝ) * ((-675339/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c147 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-756263/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6070947/10000000) (δ := 5747/500000000) (ψ := -35361/50000) 226 180
    (log_br_147).1 (log_br_147).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t147 : ((-623797130331/10000000000000 : ℚ) : ℝ) ≤ stT226 147 := by
  have hc : ((-756313/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((147 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c147).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_147).2
  have h0 : (0:ℝ) ≤ ((147 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-623797130331/10000000000000 : ℚ) : ℝ)
      = ((824787/10000000 : ℚ) : ℝ) * ((-756313/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c148 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((19519/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2240417/10000000) (δ := 11309/1000000000) (ψ := -35361/50000) 226 180
    (log_br_148).1 (log_br_148).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t148 : ((128345732163/2500000000000 : ℚ) : ℝ) ≤ stT226 148 := by
  have hc : ((312279/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((148 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c148).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_148).1
  have hw2 : ((148 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((410997/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((128345732163/2500000000000 : ℚ) : ℝ)
      = ((410997/5000000 : ℚ) : ℝ) * ((312279/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c149 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((81053/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 31287/200000) (δ := 5747/500000000) (ψ := -35361/50000) 226 180
    (log_br_149).1 (log_br_149).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t149 : ((8299629261/125000000000 : ℚ) : ℝ) ≤ stT226 149 := by
  have hc : ((10131/12500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((149 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c149).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_149).1
  have hw2 : ((149 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((819231/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8299629261/125000000000 : ℚ) : ℝ)
      = ((819231/10000000 : ℚ) : ℝ) * ((10131/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c150 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-134199/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2671789/5000000) (δ := 11309/1000000000) (ψ := -35361/50000) 226 180
    (log_br_150).1 (log_br_150).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t150 : ((-219166574231/5000000000000 : ℚ) : ℝ) ≤ stT226 150 := by
  have hc : ((-268423/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((150 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c150).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_150).2
  have h0 : (0:ℝ) ≤ ((150 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-219166574231/5000000000000 : ℚ) : ℝ)
      = ((816497/10000000 : ℚ) : ℝ) * ((-268423/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c151 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-87877/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3305093/5000000) (δ := 11401/1000000000) (ψ := -35361/50000) 226 181
    (log_br_151).1 (log_br_151).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t151 : ((-35758702449/500000000000 : ℚ) : ℝ) ≤ stT226 151 := by
  have hc : ((-43941/50000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((151 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c151).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_151).2
  have h0 : (0:ℝ) ≤ ((151 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-35758702449/500000000000 : ℚ) : ℝ)
      = ((813789/10000000 : ℚ) : ℝ) * ((-43941/50000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c152 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((101593/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2880791/10000000) (δ := 5701/500000000) (ψ := -35361/50000) 226 181
    (log_br_152).1 (log_br_152).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t152 : ((164785309227/5000000000000 : ℚ) : ℝ) ≤ stT226 152 := by
  have hc : ((203161/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((152 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c152).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_152).1
  have hw2 : ((152 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((811107/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((164785309227/5000000000000 : ℚ) : ℝ)
      = ((811107/10000000 : ℚ) : ℝ) * ((203161/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c153 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((473077/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 41207/500000) (δ := 5701/500000000) (ψ := -35361/50000) 226 181
    (log_br_153).1 (log_br_153).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t153 : ((23902489719/312500000000 : ℚ) : ℝ) ≤ stT226 153 := by
  have hc : ((118263/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((153 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c153).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_153).1
  have hw2 : ((153 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((202113/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((23902489719/312500000000 : ℚ) : ℝ)
      = ((202113/2500000 : ℚ) : ℝ) * ((118263/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c154 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-28641/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2252473/5000000) (δ := 11401/1000000000) (ψ := -35361/50000) 226 181
    (log_br_154).1 (log_br_154).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t154 : ((-92338451747/5000000000000 : ℚ) : ℝ) ≤ stT226 154 := by
  have hc : ((-114589/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((154 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c154).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_154).2
  have h0 : (0:ℝ) ≤ ((154 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92338451747/5000000000000 : ℚ) : ℝ)
      = ((805823/10000000 : ℚ) : ℝ) * ((-114589/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c155 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-124053/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1509211/2000000) (δ := 2827/250000000) (ψ := -35361/50000) 226 182
    (log_br_155).1 (log_br_155).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t155 : ((-19929374157/250000000000 : ℚ) : ℝ) ≤ stT226 155 := by
  have hc : ((-496237/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((155 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c155).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_155).2
  have h0 : (0:ℝ) ≤ ((155 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19929374157/250000000000 : ℚ) : ℝ)
      = ((40161/500000 : ℚ) : ℝ) * ((-496237/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c156 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((5757/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3912597/10000000) (δ := 2299/200000000) (ψ := -35361/50000) 226 182
    (log_br_156).1 (log_br_156).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t156 : ((7139457/15625000000 : ℚ) : ℝ) ≤ stT226 156 := by
  have hc : ((5707/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((156 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c156).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_156).1
  have hw2 : ((156 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((1251/15625 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7139457/15625000000 : ℚ) : ℝ)
      = ((1251/15625 : ℚ) : ℝ) * ((5707/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c157 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((198539/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7559/250000) (δ := 2299/200000000) (ψ := -35361/50000) 226 182
    (log_br_157).1 (log_br_157).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t157 : ((79221607747/1000000000000 : ℚ) : ℝ) ≤ stT226 157 := by
  have hc : ((198529/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((157 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c157).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_157).1
  have hw2 : ((157 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((399043/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79221607747/1000000000000 : ℚ) : ℝ)
      = ((399043/5000000 : ℚ) : ℝ) * ((198529/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c158 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((254007/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1642469/5000000) (δ := 2299/200000000) (ψ := -35361/50000) 226 182
    (log_br_158).1 (log_br_158).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t158 : ((202037269049/10000000000000 : ℚ) : ℝ) ≤ stT226 158 := by
  have hc : ((253957/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((158 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c158).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_158).1
  have hw2 : ((158 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((795557/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((202037269049/10000000000000 : ℚ) : ℝ)
      = ((795557/10000000 : ℚ) : ℝ) * ((253957/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c159 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-920383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1712409/2500000) (δ := 2299/200000000) (ψ := -35361/50000) 226 182
    (log_br_159).1 (log_br_159).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t159 : ((-182487807879/2500000000000 : ℚ) : ℝ) ≤ stT226 159 := by
  have hc : ((-920433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((159 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c159).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_159).2
  have h0 : (0:ℝ) ≤ ((159 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-182487807879/2500000000000 : ℚ) : ℝ)
      = ((198263/2500000 : ℚ) : ℝ) * ((-920433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c160 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-527457/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5316003/10000000) (δ := 2847/250000000) (ψ := -35361/50000) 226 183
    (log_br_160).1 (log_br_160).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t160 : ((-41703120899/1000000000000 : ℚ) : ℝ) ≤ stT226 160 := by
  have hc : ((-527507/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((160 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c160).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_160).2
  have h0 : (0:ℝ) ≤ ((160 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41703120899/1000000000000 : ℚ) : ℝ)
      = ((79057/1000000 : ℚ) : ℝ) * ((-527507/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c161 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((18823/25000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -179577/1000000) (δ := 2283/200000000) (ψ := -35361/50000) 226 183
    (log_br_161).1 (log_br_161).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t161 : ((5933443757/100000000000 : ℚ) : ℝ) ≤ stT226 161 := by
  have hc : ((75287/100000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((161 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c161).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_161).1
  have hw2 : ((161 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((78811/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((5933443757/100000000000 : ℚ) : ℝ)
      = ((78811/1000000 : ℚ) : ℝ) * ((75287/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c162 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((776891/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 170271/1000000) (δ := 2283/200000000) (ψ := -35361/50000) 226 183
    (log_br_162).1 (log_br_162).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t162 : ((305171887917/5000000000000 : ℚ) : ℝ) ≤ stT226 162 := by
  have hc : ((776841/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((162 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c162).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_162).1
  have hw2 : ((162 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((392837/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((305171887917/5000000000000 : ℚ) : ℝ)
      = ((392837/5000000 : ℚ) : ℝ) * ((776841/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c163 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-480363/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5179663/10000000) (δ := 2847/250000000) (ψ := -35361/50000) 226 183
    (log_br_163).1 (log_br_163).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t163 : ((-376288766793/10000000000000 : ℚ) : ℝ) ≤ stT226 163 := by
  have hc : ((-480413/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((163 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c163).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_163).2
  have h0 : (0:ℝ) ≤ ((163 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-376288766793/10000000000000 : ℚ) : ℝ)
      = ((783261/10000000 : ℚ) : ℝ) * ((-480413/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c164 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-475779/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -7072647/10000000) (δ := 11323/1000000000) (ψ := -35361/50000) 226 184
    (log_br_164).1 (log_br_164).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t164 : ((-92885148419/1250000000000 : ℚ) : ℝ) ≤ stT226 164 := by
  have hc : ((-118951/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((164 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c164).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_164).2
  have h0 : (0:ℝ) ≤ ((164 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-92885148419/1250000000000 : ℚ) : ℝ)
      = ((780869/10000000 : ℚ) : ℝ) * ((-118951/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c165 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((57667/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -909503/2500000) (δ := 11323/1000000000) (ψ := -35361/50000) 226 184
    (log_br_165).1 (log_br_165).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t165 : ((11218545429/1250000000000 : ℚ) : ℝ) ≤ stT226 165 := by
  have hc : ((28821/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((165 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c165).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_165).1
  have hw2 : ((165 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((389249/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((11218545429/1250000000000 : ℚ) : ℝ)
      = ((389249/5000000 : ℚ) : ℝ) * ((28821/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c166 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((199197/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -224113/10000000) (δ := 287/25000000) (ψ := -35361/50000) 226 184
    (log_br_166).1 (log_br_166).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t166 : ((3091979801/40000000000 : ℚ) : ℝ) ≤ stT226 166 := by
  have hc : ((199187/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((166 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c166).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_166).1
  have hw2 : ((166 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((15523/200000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3091979801/40000000000 : ℚ) : ℝ)
      = ((15523/200000 : ℚ) : ℝ) * ((199187/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c167 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((59689/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1584667/5000000) (δ := 11323/1000000000) (ψ := -35361/50000) 226 184
    (log_br_167).1 (log_br_167).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t167 : ((46180982817/2000000000000 : ℚ) : ℝ) ≤ stT226 167 := by
  have hc : ((59679/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((167 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c167).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_167).1
  have hw2 : ((167 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((773823/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((46180982817/2000000000000 : ℚ) : ℝ)
      = ((773823/10000000 : ℚ) : ℝ) * ((59679/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c168 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-216379/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 163561/250000) (δ := 287/25000000) (ψ := -35361/50000) 226 184
    (log_br_168).1 (log_br_168).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t168 : ((-333899441811/5000000000000 : ℚ) : ℝ) ≤ stT226 168 := by
  have hc : ((-432783/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((168 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c168).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_168).2
  have h0 : (0:ℝ) ≤ ((168 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333899441811/5000000000000 : ℚ) : ℝ)
      = ((771517/10000000 : ℚ) : ℝ) * ((-432783/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c169 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-171167/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5812361/10000000) (δ := 11373/1000000000) (ψ := -35361/50000) 226 185
    (log_br_169).1 (log_br_169).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t169 : ((-263353155929/5000000000000 : ℚ) : ℝ) ≤ stT226 169 := by
  have hc : ((-342359/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((169 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c169).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_169).2
  have h0 : (0:ℝ) ≤ ((169 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-263353155929/5000000000000 : ℚ) : ℝ)
      = ((769231/10000000 : ℚ) : ℝ) * ((-342359/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c170 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((547341/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -247903/1000000) (δ := 1143/100000000) (ψ := -35361/50000) 226 185
    (log_br_170).1 (log_br_170).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t170 : ((104938123631/2500000000000 : ℚ) : ℝ) ≤ stT226 170 := by
  have hc : ((547291/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((170 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c170).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_170).1
  have hw2 : ((170 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((191741/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((104938123631/2500000000000 : ℚ) : ℝ)
      = ((191741/2500000 : ℚ) : ℝ) * ((547291/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c171 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((944771/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 834751/10000000) (δ := 11373/1000000000) (ψ := -35361/50000) 226 185
    (log_br_171).1 (log_br_171).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t171 : ((722446098399/10000000000000 : ℚ) : ℝ) ≤ stT226 171 := by
  have hc : ((944721/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((171 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c171).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_171).1
  have hw2 : ((171 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((764719/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((722446098399/10000000000000 : ℚ) : ℝ)
      = ((764719/10000000 : ℚ) : ℝ) * ((944721/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c172 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-80799/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 412921/1000000) (δ := 1143/100000000) (ψ := -35361/50000) 226 185
    (log_br_172).1 (log_br_172).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t172 : ((-61646796557/10000000000000 : ℚ) : ℝ) ≤ stT226 172 := by
  have hc : ((-80849/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((172 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c172).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_172).2
  have h0 : (0:ℝ) ≤ ((172 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61646796557/10000000000000 : ℚ) : ℝ)
      = ((762493/10000000 : ℚ) : ℝ) * ((-80849/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c173 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-491943/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7404571/10000000) (δ := 11373/1000000000) (ψ := -35361/50000) 226 185
    (log_br_173).1 (log_br_173).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t173 : ((-2922159241/39062500000 : ℚ) : ℝ) ≤ stT226 173 := by
  have hc : ((-15374/15625 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((173 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c173).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_173).2
  have h0 : (0:ℝ) ≤ ((173 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2922159241/39062500000 : ℚ) : ℝ)
      = ((380143/5000000 : ℚ) : ℝ) * ((-15374/15625 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c174 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-108283/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2523451/5000000) (δ := 5733/500000000) (ψ := -35361/50000) 226 186
    (log_br_174).1 (log_br_174).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t174 : ((-164197420509/5000000000000 : ℚ) : ℝ) ≤ stT226 174 := by
  have hc : ((-216591/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((174 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c174).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_174).2
  have h0 : (0:ℝ) ≤ ((174 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-164197420509/5000000000000 : ℚ) : ℝ)
      = ((758099/10000000 : ℚ) : ℝ) * ((-216591/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c175 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((187353/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -56533/312500) (δ := 11337/1000000000) (ψ := -35361/50000) 226 186
    (log_br_175).1 (log_br_175).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t175 : ((35403982371/625000000000 : ℚ) : ℝ) ≤ stT226 175 := by
  have hc : ((374681/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((175 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c175).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_175).1
  have hw2 : ((175 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((94491/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((35403982371/625000000000 : ℚ) : ℝ)
      = ((94491/1250000 : ℚ) : ℝ) * ((374681/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c176 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((13204/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 705157/5000000) (δ := 11337/1000000000) (ψ := -35361/50000) 226 186
    (log_br_176).1 (log_br_176).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t176 : ((159236733167/2500000000000 : ℚ) : ℝ) ≤ stT226 176 := by
  have hc : ((422503/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((176 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c176).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_176).1
  have hw2 : ((176 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((376889/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((159236733167/2500000000000 : ℚ) : ℝ)
      = ((376889/5000000 : ℚ) : ℝ) * ((422503/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c177 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-33799/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4611491/10000000) (δ := 11337/1000000000) (ψ := -35361/50000) 226 186
    (log_br_177).1 (log_br_177).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t177 : ((-101638458987/5000000000000 : ℚ) : ℝ) ≤ stT226 177 := by
  have hc : ((-135221/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((177 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c177).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_177).2
  have h0 : (0:ℝ) ≤ ((177 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-101638458987/5000000000000 : ℚ) : ℝ)
      = ((751647/10000000 : ℚ) : ℝ) * ((-135221/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c178 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-499859/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1948647/2500000) (δ := 11337/1000000000) (ψ := -35361/50000) 226 186
    (log_br_178).1 (log_br_178).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t178 : ((-23417440893/312500000000 : ℚ) : ℝ) ≤ stT226 178 := by
  have hc : ((-124971/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((178 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c178).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_178).2
  have h0 : (0:ℝ) ≤ ((178 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23417440893/312500000000 : ℚ) : ℝ)
      = ((187383/2500000 : ℚ) : ℝ) * ((-124971/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c179 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-322561/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1187019/2500000) (δ := 11359/1000000000) (ψ := -35361/50000) 226 187
    (log_br_179).1 (log_br_179).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t179 : ((-60282768849/2500000000000 : ℚ) : ℝ) ≤ stT226 179 := by
  have hc : ((-322611/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((179 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c179).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_179).2
  have h0 : (0:ℝ) ≤ ((179 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-60282768849/2500000000000 : ℚ) : ℝ)
      = ((186859/2500000 : ℚ) : ℝ) * ((-322611/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c180 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((400993/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1600461/10000000) (δ := 11359/1000000000) (ψ := -35361/50000) 226 187
    (log_br_180).1 (log_br_180).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t180 : ((7471587591/125000000000 : ℚ) : ℝ) ≤ stT226 180 := by
  have hc : ((50121/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((180 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c180).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_180).1
  have hw2 : ((180 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((149071/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((7471587591/125000000000 : ℚ) : ℝ)
      = ((149071/2000000 : ℚ) : ℝ) * ((50121/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c181 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((409279/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 191219/1250000) (δ := 11359/1000000000) (ψ := -35361/50000) 226 187
    (log_br_181).1 (log_br_181).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t181 : ((76049010669/1250000000000 : ℚ) : ℝ) ≤ stT226 181 := by
  have hc : ((204627/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((181 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c181).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_181).1
  have hw2 : ((181 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((371647/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((76049010669/1250000000000 : ℚ) : ℝ)
      = ((371647/5000000 : ℚ) : ℝ) * ((204627/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c182 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-14119/50000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1160669/2500000) (δ := 11359/1000000000) (ψ := -35361/50000) 226 187
    (log_br_182).1 (log_br_182).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t182 : ((-16748099/800000000 : ℚ) : ℝ) ≤ stT226 182 := by
  have hc : ((-28243/100000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((182 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c182).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_182).2
  have h0 : (0:ℝ) ≤ ((182 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16748099/800000000 : ℚ) : ℝ)
      = ((593/8000 : ℚ) : ℝ) * ((-28243/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c183 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-199787/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3869297/5000000) (δ := 2861/250000000) (ψ := -35361/50000) 226 187
    (log_br_183).1 (log_br_183).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t183 : ((-73847168967/1000000000000 : ℚ) : ℝ) ≤ stT226 183 := by
  have hc : ((-199797/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((183 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c183).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_183).2
  have h0 : (0:ℝ) ≤ ((183 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-73847168967/1000000000000 : ℚ) : ℝ)
      = ((369611/5000000 : ℚ) : ℝ) * ((-199797/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c184 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-93969/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2445173/5000000) (δ := 2863/250000000) (ψ := -35361/50000) 226 188
    (log_br_184).1 (log_br_184).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t184 : ((-13856820323/500000000000 : ℚ) : ℝ) ≤ stT226 184 := by
  have hc : ((-187963/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((184 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c184).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_184).2
  have h0 : (0:ℝ) ≤ ((184 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-13856820323/500000000000 : ℚ) : ℝ)
      = ((73721/1000000 : ℚ) : ℝ) * ((-187963/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c185 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((744377/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1827989/10000000) (δ := 11351/1000000000) (ψ := -35361/50000) 226 188
    (log_br_185).1 (log_br_185).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t185 : ((273619815489/5000000000000 : ℚ) : ℝ) ≤ stT226 185 := by
  have hc : ((744327/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((185 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c185).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_185).1
  have hw2 : ((185 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((367607/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((273619815489/5000000000000 : ℚ) : ℝ)
      = ((367607/5000000 : ℚ) : ℝ) * ((744327/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c186 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((441841/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1217813/10000000) (δ := 11351/1000000000) (ψ := -35361/50000) 226 188
    (log_br_186).1 (log_br_186).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t186 : ((8098873869/125000000000 : ℚ) : ℝ) ≤ stT226 186 := by
  have hc : ((55227/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((186 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c186).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_186).1
  have hw2 : ((186 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((146647/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8098873869/125000000000 : ℚ) : ℝ)
      = ((146647/2000000 : ℚ) : ℝ) * ((55227/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c187 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-12779/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4247343/10000000) (δ := 11351/1000000000) (ψ := -35361/50000) 226 188
    (log_br_187).1 (log_br_187).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t187 : ((-584287127/62500000000 : ℚ) : ℝ) ≤ stT226 187 := by
  have hc : ((-799/6250 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((187 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c187).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_187).2
  have h0 : (0:ℝ) ≤ ((187 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-584287127/62500000000 : ℚ) : ℝ)
      = ((731273/10000000 : ℚ) : ℝ) * ((-799/6250 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c188 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-971969/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 7260657/10000000) (δ := 2863/250000000) (ψ := -35361/50000) 226 188
    (log_br_188).1 (log_br_188).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t188 : ((-28356710287/400000000000 : ℚ) : ℝ) ≤ stT226 188 := by
  have hc : ((-972019/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((188 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c188).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_188).2
  have h0 : (0:ℝ) ≤ ((188 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-28356710287/400000000000 : ℚ) : ℝ)
      = ((29173/400000 : ℚ) : ℝ) * ((-972019/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c189 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-57219/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1362481/2500000) (δ := 5729/500000000) (ψ := -35361/50000) 226 189
    (log_br_189).1 (log_br_189).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t189 : ((-5203042129/125000000000 : ℚ) : ℝ) ≤ stT226 189 := by
  have hc : ((-7153/12500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((189 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c189).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_189).2
  have h0 : (0:ℝ) ≤ ((189 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5203042129/125000000000 : ℚ) : ℝ)
      = ((727393/10000000 : ℚ) : ℝ) * ((-7153/12500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c190 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((550889/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2468419/10000000) (δ := 5729/500000000) (ψ := -35361/50000) 226 189
    (log_br_190).1 (log_br_190).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t190 : ((99905118591/2500000000000 : ℚ) : ℝ) ≤ stT226 190 := by
  have hc : ((550839/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((190 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c190).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_190).1
  have hw2 : ((190 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((181369/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((99905118591/2500000000000 : ℚ) : ℝ)
      = ((181369/2500000 : ℚ) : ℝ) * ((550839/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c191 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((196053/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 124373/2500000) (δ := 5729/500000000) (ψ := -35361/50000) 226 189
    (log_br_191).1 (log_br_191).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t191 : ((70925808841/1000000000000 : ℚ) : ℝ) ≤ stT226 191 := by
  have hc : ((196043/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((191 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c191).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_191).1
  have hw2 : ((191 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((361787/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((70925808841/1000000000000 : ℚ) : ℝ)
      = ((361787/5000000 : ℚ) : ℝ) * ((196043/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c192 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((190479/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 689573/2000000) (δ := 2269/200000000) (ψ := -35361/50000) 226 189
    (log_br_192).1 (log_br_192).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t192 : ((137430133723/10000000000000 : ℚ) : ℝ) ≤ stT226 192 := by
  have hc : ((190429/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((192 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c192).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_192).1
  have hw2 : ((192 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((721687/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((137430133723/10000000000000 : ℚ) : ℝ)
      = ((721687/10000000 : ℚ) : ℝ) * ((190429/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c193 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-415909/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6382927/10000000) (δ := 2269/200000000) (ψ := -35361/50000) 226 189
    (log_br_193).1 (log_br_193).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t193 : ((-18712246759/312500000000 : ℚ) : ℝ) ≤ stT226 193 := by
  have hc : ((-207967/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((193 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c193).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_193).2
  have h0 : (0:ℝ) ≤ ((193 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18712246759/312500000000 : ℚ) : ℝ)
      = ((89977/1250000 : ℚ) : ℝ) * ((-207967/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c194 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-836711/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1601279/2500000) (δ := 5683/500000000) (ψ := -35361/50000) 226 190
    (log_br_194).1 (log_br_194).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t194 : ((-600760090799/10000000000000 : ℚ) : ℝ) ≤ stT226 194 := by
  have hc : ((-836761/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((194 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c194).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_194).2
  have h0 : (0:ℝ) ≤ ((194 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-600760090799/10000000000000 : ℚ) : ℝ)
      = ((717959/10000000 : ℚ) : ℝ) * ((-836761/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c195 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((84939/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -140009/400000) (δ := 5683/500000000) (ψ := -35361/50000) 226 190
    (log_br_195).1 (log_br_195).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t195 : ((15202026049/1250000000000 : ℚ) : ℝ) ≤ stT226 195 := by
  have hc : ((42457/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((195 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c195).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_195).1
  have hw2 : ((195 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((358057/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15202026049/1250000000000 : ℚ) : ℝ)
      = ((358057/5000000 : ℚ) : ℝ) * ((42457/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c196 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((970361/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -305097/5000000) (δ := 11437/1000000000) (ψ := -35361/50000) 226 190
    (log_br_196).1 (log_br_196).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t196 : ((138615718527/2000000000000 : ℚ) : ℝ) ≤ stT226 196 := by
  have hc : ((970311/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((196 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c196).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_196).1
  have hw2 : ((196 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((142857/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((138615718527/2000000000000 : ℚ) : ℝ)
      = ((142857/2000000 : ℚ) : ℝ) * ((970311/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c197 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((154213/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 566287/2500000) (δ := 5683/500000000) (ψ := -35361/50000) 226 190
    (log_br_197).1 (log_br_197).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t197 : ((21972646047/500000000000 : ℚ) : ℝ) ≤ stT226 197 := by
  have hc : ((308401/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((197 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c197).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_197).1
  have hw2 : ((197 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((71247/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((21972646047/500000000000 : ℚ) : ℝ)
      = ((71247/1000000 : ℚ) : ℝ) * ((308401/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c198 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-115349/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 640739/1250000) (δ := 11437/1000000000) (ψ := -35361/50000) 226 190
    (log_br_198).1 (log_br_198).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t198 : ((-16396791441/500000000000 : ℚ) : ℝ) ≤ stT226 198 := by
  have hc : ((-230723/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((198 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c198).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_198).2
  have h0 : (0:ℝ) ≤ ((198 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-16396791441/500000000000 : ℚ) : ℝ)
      = ((71067/1000000 : ℚ) : ℝ) * ((-230723/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c199 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-998881/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3867847/5000000) (δ := 1133/100000000) (ψ := -35361/50000) 226 191
    (log_br_199).1 (log_br_199).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t199 : ((-354062102571/5000000000000 : ℚ) : ℝ) ≤ stT226 199 := by
  have hc : ((-998931/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((199 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c199).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_199).2
  have h0 : (0:ℝ) ≤ ((199 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-354062102571/5000000000000 : ℚ) : ℝ)
      = ((354441/5000000 : ℚ) : ℝ) * ((-998931/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c200 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-76159/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -4903631/10000000) (δ := 11473/1000000000) (ψ := -35361/50000) 226 191
    (log_br_200).1 (log_br_200).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t200 : ((-53859633083/2000000000000 : ℚ) : ℝ) ≤ stT226 200 := by
  have hc : ((-76169/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((200 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c200).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_200).2
  have h0 : (0:ℝ) ≤ ((200 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-53859633083/2000000000000 : ℚ) : ℝ)
      = ((707107/10000000 : ℚ) : ℝ) * ((-76169/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c201 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((67173/100000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2085637/10000000) (δ := 11473/1000000000) (ψ := -35361/50000) 226 191
    (log_br_201).1 (log_br_201).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t201 : ((296103831/6250000000 : ℚ) : ℝ) ≤ stT226 201 := by
  have hc : ((2099/3125 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((201 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c201).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_201).1
  have hw2 : ((201 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((141069/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((296103831/6250000000 : ℚ) : ℝ)
      = ((141069/2000000 : ℚ) : ℝ) * ((2099/3125 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c202 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((29969/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 44893/625000) (δ := 1133/100000000) (ψ := -35361/50000) 226 191
    (log_br_202).1 (log_br_202).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t202 : ((337359985963/5000000000000 : ℚ) : ℝ) ≤ stT226 202 := by
  have hc : ((479479/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((202 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c202).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_202).1
  have hw2 : ((202 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((703597/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((337359985963/5000000000000 : ℚ) : ℝ)
      = ((703597/10000000 : ℚ) : ℝ) * ((479479/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c203 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((41661/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 877107/2500000) (δ := 11473/1000000000) (ψ := -35361/50000) 226 191
    (log_br_203).1 (log_br_203).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t203 : ((29231499507/2500000000000 : ℚ) : ℝ) ≤ stT226 203 := by
  have hc : ((83297/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((203 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c203).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_203).1
  have hw2 : ((203 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((350931/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29231499507/2500000000000 : ℚ) : ℝ)
      = ((350931/5000000 : ℚ) : ℝ) * ((83297/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c204 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-161881/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3142419/5000000) (δ := 11473/1000000000) (ψ := -35361/50000) 226 191
    (log_br_204).1 (log_br_204).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t204 : ((-113346526631/2000000000000 : ℚ) : ℝ) ≤ stT226 204 := by
  have hc : ((-161891/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((204 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c204).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_204).2
  have h0 : (0:ℝ) ≤ ((204 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-113346526631/2000000000000 : ℚ) : ℝ)
      = ((700141/10000000 : ℚ) : ℝ) * ((-161891/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c205 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-177631/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1665069/2500000) (δ := 11423/1000000000) (ψ := -35361/50000) 226 192
    (log_br_205).1 (log_br_205).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t205 : ((-124069981271/2000000000000 : ℚ) : ℝ) ≤ stT226 205 := by
  have hc : ((-177641/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((205 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c205).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_205).2
  have h0 : (0:ℝ) ≤ ((205 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-124069981271/2000000000000 : ℚ) : ℝ)
      = ((698431/10000000 : ℚ) : ℝ) * ((-177641/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c206 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((6447/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3910873/10000000) (δ := 11423/1000000000) (ψ := -35361/50000) 226 192
    (log_br_206).1 (log_br_206).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t206 : ((4457001001/10000000000000 : ℚ) : ℝ) ≤ stT226 206 := by
  have hc : ((6397/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((206 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c206).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_206).1
  have hw2 : ((206 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((696733/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((4457001001/10000000000000 : ℚ) : ℝ)
      = ((696733/10000000 : ℚ) : ℝ) * ((6397/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c207 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((222901/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -293701/2500000) (δ := 11423/1000000000) (ψ := -35361/50000) 226 192
    (log_br_207).1 (log_br_207).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t207 : ((38729551537/625000000000 : ℚ) : ℝ) ≤ stT226 207 := by
  have hc : ((445777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((207 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c207).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_207).1
  have hw2 : ((207 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((86881/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((38729551537/625000000000 : ℚ) : ℝ)
      = ((86881/1250000 : ℚ) : ℝ) * ((445777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c208 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((10179/12500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1548101/10000000) (δ := 569/50000000) (ψ := -35361/50000) 226 192
    (log_br_208).1 (log_br_208).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t208 : ((451675569/8000000000 : ℚ) : ℝ) ≤ stT226 208 := by
  have hc : ((81427/100000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((208 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c208).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_208).1
  have hw2 : ((208 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((5547/80000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((451675569/8000000000 : ℚ) : ℝ)
      = ((5547/80000 : ℚ) : ℝ) * ((81427/100000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c209 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-131999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2128977/5000000) (δ := 569/50000000) (ψ := -35361/50000) 226 192
    (log_br_209).1 (log_br_209).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t209 : ((-18268054807/2000000000000 : ℚ) : ℝ) ≤ stT226 209 := by
  have hc : ((-132049/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((209 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c209).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_209).2
  have h0 : (0:ℝ) ≤ ((209 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-18268054807/2000000000000 : ℚ) : ℝ)
      = ((138343/2000000 : ℚ) : ℝ) * ((-132049/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c210 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-468011/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1738717/2500000) (δ := 11423/1000000000) (ψ := -35361/50000) 226 192
    (log_br_210).1 (log_br_210).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t210 : ((-40371966297/625000000000 : ℚ) : ℝ) ≤ stT226 210 := by
  have hc : ((-117009/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((210 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c210).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_210).2
  have h0 : (0:ℝ) ≤ ((210 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-40371966297/625000000000 : ℚ) : ℝ)
      = ((345033/5000000 : ℚ) : ℝ) * ((-117009/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c211 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-151151/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3034503/5000000) (δ := 2829/250000000) (ψ := -35361/50000) 226 193
    (log_br_211).1 (log_br_211).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t211 : ((-104063616069/2000000000000 : ℚ) : ℝ) ≤ stT226 211 := by
  have hc : ((-151161/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((211 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c211).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_211).2
  have h0 : (0:ℝ) ≤ ((211 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-104063616069/2000000000000 : ℚ) : ℝ)
      = ((688429/10000000 : ℚ) : ℝ) * ((-151161/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c212 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((105083/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3397629/10000000) (δ := 11487/1000000000) (ψ := -35361/50000) 226 193
    (log_br_212).1 (log_br_212).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t212 : ((18038511129/1250000000000 : ℚ) : ℝ) ≤ stT226 212 := by
  have hc : ((52529/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((212 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c212).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_212).1
  have hw2 : ((212 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((343401/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((18038511129/1250000000000 : ℚ) : ℝ)
      = ((343401/5000000 : ℚ) : ℝ) * ((52529/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c213 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((956651/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -184699/2500000) (δ := 2829/250000000) (ψ := -35361/50000) 226 193
    (log_br_213).1 (log_br_213).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t213 : ((163862881497/2500000000000 : ℚ) : ℝ) ≤ stT226 213 := by
  have hc : ((956601/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((213 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c213).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_213).1
  have hw2 : ((213 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((171297/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((163862881497/2500000000000 : ℚ) : ℝ)
      = ((171297/2500000 : ℚ) : ℝ) * ((956601/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c214 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((45171/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 238451/1250000) (δ := 11487/1000000000) (ψ := -35361/50000) 226 193
    (log_br_214).1 (log_br_214).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t214 : ((49401730931/1000000000000 : ℚ) : ℝ) ≤ stT226 214 := by
  have hc : ((361343/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((214 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c214).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_214).1
  have hw2 : ((214 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((136717/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((49401730931/1000000000000 : ℚ) : ℝ)
      = ((136717/2000000 : ℚ) : ℝ) * ((361343/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c215 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-243389/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2270819/5000000) (δ := 11487/1000000000) (ψ := -35361/50000) 226 193
    (log_br_215).1 (log_br_215).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t215 : ((-33204836161/2000000000000 : ℚ) : ℝ) ≤ stT226 215 := by
  have hc : ((-243439/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((215 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c215).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_215).2
  have h0 : (0:ℝ) ≤ ((215 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-33204836161/2000000000000 : ℚ) : ℝ)
      = ((136399/2000000 : ℚ) : ℝ) * ((-243439/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c216 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-962097/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 895433/1250000) (δ := 11487/1000000000) (ψ := -35361/50000) 226 193
    (log_br_216).1 (log_br_216).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t216 : ((-327329144429/5000000000000 : ℚ) : ℝ) ≤ stT226 216 := by
  have hc : ((-962147/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((216 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c216).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_216).2
  have h0 : (0:ℝ) ≤ ((216 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-327329144429/5000000000000 : ℚ) : ℝ)
      = ((340207/5000000 : ℚ) : ℝ) * ((-962147/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c217 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-143907/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5934821/10000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 194
    (log_br_217).1 (log_br_217).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t217 : ((-19539467173/400000000000 : ℚ) : ℝ) ≤ stT226 217 := by
  have hc : ((-143917/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((217 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c217).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_217).2
  have h0 : (0:ℝ) ≤ ((217 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-19539467173/400000000000 : ℚ) : ℝ)
      = ((135769/2000000 : ℚ) : ℝ) * ((-143917/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c218 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((46753/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3337121/10000000) (δ := 11409/1000000000) (ψ := -35361/50000) 226 194
    (log_br_218).1 (log_br_218).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t218 : ((6331666551/400000000000 : ℚ) : ℝ) ≤ stT226 218 := by
  have hc : ((46743/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((218 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c218).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_218).1
  have hw2 : ((218 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((135457/2000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((6331666551/400000000000 : ℚ) : ℝ)
      = ((135457/2000000 : ℚ) : ℝ) * ((46743/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c219 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((59699/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -150257/2000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 194
    (log_br_219).1 (log_br_219).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t219 : ((322709691879/5000000000000 : ℚ) : ℝ) ≤ stT226 219 := by
  have hc : ((477567/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((219 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c219).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_219).1
  have hw2 : ((219 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((675737/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((322709691879/5000000000000 : ℚ) : ℝ)
      = ((675737/10000000 : ℚ) : ℝ) * ((477567/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c220 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((46611/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 911371/5000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 194
    (log_br_220).1 (log_br_220).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t220 : ((251383861737/5000000000000 : ℚ) : ℝ) ≤ stT226 220 := by
  have hc : ((372863/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((220 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c220).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_220).1
  have hw2 : ((220 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((674199/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((251383861737/5000000000000 : ℚ) : ℝ)
      = ((674199/10000000 : ℚ) : ℝ) * ((372863/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c221 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-22779/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 438513/1000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 194
    (log_br_221).1 (log_br_221).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t221 : ((-61308089893/5000000000000 : ℚ) : ℝ) ≤ stT226 221 := by
  have hc : ((-91141/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((221 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c221).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_221).2
  have h0 : (0:ℝ) ≤ ((221 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-61308089893/5000000000000 : ℚ) : ℝ)
      = ((672673/10000000 : ℚ) : ℝ) * ((-91141/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c222 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-933321/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6935879/10000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 194
    (log_br_222).1 (log_br_222).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t222 : ((-626438480247/10000000000000 : ℚ) : ℝ) ≤ stT226 222 := by
  have hc : ((-933371/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((222 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c222).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_222).2
  have h0 : (0:ℝ) ≤ ((222 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-626438480247/10000000000000 : ℚ) : ℝ)
      = ((671157/10000000 : ℚ) : ℝ) * ((-933371/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c223 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-159399/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -6232749/10000000) (δ := 11501/1000000000) (ψ := -35361/50000) 226 195
    (log_br_223).1 (log_br_223).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t223 : ((-2134964737/40000000000 : ℚ) : ℝ) ≤ stT226 223 := by
  have hc : ((-159409/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((223 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c223).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_223).2
  have h0 : (0:ℝ) ≤ ((223 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-2134964737/40000000000 : ℚ) : ℝ)
      = ((13393/200000 : ℚ) : ℝ) * ((-159409/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c224 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((22193/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3704769/10000000) (δ := 5651/500000000) (ψ := -35361/50000) 226 195
    (log_br_224).1 (log_br_224).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t224 : ((29639935233/5000000000000 : ℚ) : ℝ) ≤ stT226 224 := by
  have hc : ((44361/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((224 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c224).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_224).1
  have hw2 : ((224 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((668153/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((29639935233/5000000000000 : ℚ) : ℝ)
      = ((668153/10000000 : ℚ) : ℝ) * ((44361/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c225 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((177839/200000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1188033/10000000) (δ := 5651/500000000) (ψ := -35361/50000) 226 195
    (log_br_225).1 (log_br_225).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t225 : ((59276274057/1000000000000 : ℚ) : ℝ) ≤ stT226 225 := by
  have hc : ((177829/200000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((225 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c225).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_225).1
  have hw2 : ((225 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((333333/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((59276274057/1000000000000 : ℚ) : ℝ)
      = ((333333/5000000 : ℚ) : ℝ) * ((177829/200000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c226 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((432161/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 82343/625000) (δ := 11351/500000000) (ψ := -35361/50000) 226 195
    (log_br_226).1 (log_br_226).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t226 : ((3593156823/62500000000 : ℚ) : ℝ) ≤ stT226 226 := by
  have hc : ((54017/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((226 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c226).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_226).1
  have hw2 : ((226 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((66519/1000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((3593156823/62500000000 : ℚ) : ℝ)
      = ((66519/1000000 : ℚ) : ℝ) * ((54017/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c227 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((1437/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3811991/10000000) (δ := 5651/500000000) (ψ := -35361/50000) 226 195
    (log_br_227).1 (log_br_227).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t227 : ((15243726141/5000000000000 : ℚ) : ℝ) ≤ stT226 227 := by
  have hc : ((22967/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((227 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c227).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_227).1
  have hw2 : ((227 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((663723/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((15243726141/5000000000000 : ℚ) : ℝ)
      = ((663723/10000000 : ℚ) : ℝ) * ((22967/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c228 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-12686/15625 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1259101/2000000) (δ := 5651/500000000) (ψ := -35361/50000) 226 195
    (log_br_228).1 (log_br_228).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t228 : ((-268865169859/5000000000000 : ℚ) : ℝ) ≤ stT226 228 := by
  have hc : ((-405977/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((228 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c228).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_228).2
  have h0 : (0:ℝ) ≤ ((228 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-268865169859/5000000000000 : ℚ) : ℝ)
      = ((662267/10000000 : ℚ) : ℝ) * ((-405977/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c229 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-466941/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -433737/625000) (δ := 11409/1000000000) (ψ := -35361/50000) 226 196
    (log_br_229).1 (log_br_229).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t229 : ((-154290002577/2500000000000 : ℚ) : ℝ) ≤ stT226 229 := by
  have hc : ((-233483/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((229 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c229).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_229).2
  have h0 : (0:ℝ) ≤ ((229 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-154290002577/2500000000000 : ℚ) : ℝ)
      = ((660819/10000000 : ℚ) : ℝ) * ((-233483/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c230 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-6831/31250 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2238959/5000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 196
    (log_br_230).1 (log_br_230).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t230 : ((-72084190301/5000000000000 : ℚ) : ℝ) ≤ stT226 230 := by
  have hc : ((-109321/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((230 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c230).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_230).2
  have h0 : (0:ℝ) ≤ ((230 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-72084190301/5000000000000 : ℚ) : ℝ)
      = ((659381/10000000 : ℚ) : ℝ) * ((-109321/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c231 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((688999/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1013361/5000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 196
    (log_br_231).1 (log_br_231).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t231 : ((453294683499/10000000000000 : ℚ) : ℝ) ≤ stT226 231 := by
  have hc : ((688949/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((231 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c231).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_231).1
  have hw2 : ((231 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((657951/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((453294683499/10000000000000 : ℚ) : ℝ)
      = ((657951/10000000 : ℚ) : ℝ) * ((688949/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c232 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((986329/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 103463/2500000) (δ := 5697/500000000) (ψ := -35361/50000) 226 196
    (log_br_232).1 (log_br_232).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t232 : ((161880931107/2500000000000 : ℚ) : ℝ) ≤ stT226 232 := by
  have hc : ((986279/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((232 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c232).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_232).1
  have hw2 : ((232 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((164133/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((161880931107/2500000000000 : ℚ) : ℝ)
      = ((164133/2500000 : ℚ) : ℝ) * ((986279/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c233 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((419783/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1421987/5000000) (δ := 11409/1000000000) (ψ := -35361/50000) 226 196
    (log_br_233).1 (log_br_233).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t233 : ((274975902693/10000000000000 : ℚ) : ℝ) ≤ stT226 233 := by
  have hc : ((419733/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((233 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c233).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_233).1
  have hw2 : ((233 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((655121/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((274975902693/10000000000000 : ℚ) : ℝ)
      = ((655121/10000000 : ℚ) : ℝ) * ((419733/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c234 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-509569/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 5263699/10000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 196
    (log_br_234).1 (log_br_234).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t234 : ((-333148642299/10000000000000 : ℚ) : ℝ) ≤ stT226 234 := by
  have hc : ((-509619/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((234 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c234).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_234).2
  have h0 : (0:ℝ) ≤ ((234 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-333148642299/10000000000000 : ℚ) : ℝ)
      = ((653721/10000000 : ℚ) : ℝ) * ((-509619/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c235 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-997383/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 1534617/2000000) (δ := 5697/500000000) (ψ := -35361/50000) 226 196
    (log_br_235).1 (log_br_235).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t235 : ((-650654471457/10000000000000 : ℚ) : ℝ) ≤ stT226 235 := by
  have hc : ((-997433/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((235 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c235).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_235).2
  have h0 : (0:ℝ) ≤ ((235 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-650654471457/10000000000000 : ℚ) : ℝ)
      = ((652329/10000000 : ℚ) : ℝ) * ((-997433/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c236 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-39469/62500 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -5635719/10000000) (δ := 11487/1000000000) (ψ := -35361/50000) 226 197
    (log_br_236).1 (log_br_236).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t236 : ((-41110691853/1000000000000 : ℚ) : ℝ) ≤ stT226 236 := by
  have hc : ((-315777/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((236 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c236).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_236).2
  have h0 : (0:ℝ) ≤ ((236 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-41110691853/1000000000000 : ℚ) : ℝ)
      = ((130189/2000000 : ℚ) : ℝ) * ((-315777/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c237 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((268759/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -3246729/10000000) (δ := 2829/250000000) (ψ := -35361/50000) 226 197
    (log_br_237).1 (log_br_237).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t237 : ((174545036421/10000000000000 : ℚ) : ℝ) ≤ stT226 237 := by
  have hc : ((268709/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((237 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c237).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_237).1
  have hw2 : ((237 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((649569/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((174545036421/10000000000000 : ℚ) : ℝ)
      = ((649569/10000000 : ℚ) : ℝ) * ((268709/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c238 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((940357/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -867797/10000000) (δ := 11487/1000000000) (ψ := -35361/50000) 226 197
    (log_br_238).1 (log_br_238).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t238 : ((609509818321/10000000000000 : ℚ) : ℝ) ≤ stT226 238 := by
  have hc : ((940307/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((238 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c238).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_238).1
  have hw2 : ((238 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((648203/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((609509818321/10000000000000 : ℚ) : ℝ)
      = ((648203/10000000 : ℚ) : ℝ) * ((940307/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c239 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((412533/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 187649/1250000) (δ := 2829/250000000) (ψ := -35361/50000) 226 197
    (log_br_239).1 (log_br_239).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t239 : ((33353643721/625000000000 : ℚ) : ℝ) ≤ stT226 239 := by
  have hc : ((103127/125000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((239 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c239).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_239).1
  have hw2 : ((239 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((323423/5000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((33353643721/625000000000 : ℚ) : ℝ)
      = ((323423/5000000 : ℚ) : ℝ) * ((103127/125000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c240 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((6669/250000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 3860293/10000000) (δ := 2829/250000000) (ψ := -35361/50000) 226 197
    (log_br_240).1 (log_br_240).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t240 : ((8593501561/5000000000000 : ℚ) : ℝ) ≤ stT226 240 := by
  have hc : ((13313/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((240 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c240).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_240).1
  have hw2 : ((240 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((645497/10000000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((8593501561/5000000000000 : ℚ) : ℝ)
      = ((645497/10000000 : ℚ) : ℝ) * ((13313/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c241 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-791359/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6209563/10000000) (δ := 2829/250000000) (ψ := -35361/50000) 226 197
    (log_br_241).1 (log_br_241).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t241 : ((-509791647213/10000000000000 : ℚ) : ℝ) ≤ stT226 241 := by
  have hc : ((-791409/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((241 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c241).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_241).2
  have h0 : (0:ℝ) ≤ ((241 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-509791647213/10000000000000 : ℚ) : ℝ)
      = ((644157/10000000 : ℚ) : ℝ) * ((-791409/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c242 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-120199/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -111857/156250) (δ := 11423/1000000000) (ψ := -35361/50000) 226 198
    (log_br_242).1 (log_br_242).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t242 : ((-12363350373/200000000000 : ℚ) : ℝ) ≤ stT226 242 := by
  have hc : ((-480821/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((242 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c242).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_242).2
  have h0 : (0:ℝ) ≤ ((242 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-12363350373/200000000000 : ℚ) : ℝ)
      = ((25713/400000 : ℚ) : ℝ) * ((-480821/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c243 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-353011/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -2414479/5000000) (δ := 569/50000000) (ψ := -35361/50000) 226 198
    (log_br_243).1 (log_br_243).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t243 : ((-226488984561/10000000000000 : ℚ) : ℝ) ≤ stT226 243 := by
  have hc : ((-353061/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((243 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c243).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_243).2
  have h0 : (0:ℝ) ≤ ((243 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-226488984561/10000000000000 : ℚ) : ℝ)
      = ((641501/10000000 : ℚ) : ℝ) * ((-353061/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c244 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((537399/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -313577/1250000) (δ := 569/50000000) (ψ := -35361/50000) 226 198
    (log_br_244).1 (log_br_244).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t244 : ((43000279027/1250000000000 : ℚ) : ℝ) ≤ stT226 244 := by
  have hc : ((537349/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((244 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c244).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_244).1
  have hw2 : ((244 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((80023/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((43000279027/1250000000000 : ℚ) : ℝ)
      = ((80023/1250000 : ℚ) : ℝ) * ((537349/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c245 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((124609/125000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -98897/5000000) (δ := 22623/1000000000) (ψ := -35361/50000) 226 198
    (log_br_245).1 (log_br_245).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t245 : ((79605706509/1250000000000 : ℚ) : ℝ) ≤ stT226 245 := by
  have hc : ((498411/500000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((245 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c245).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_245).1
  have hw2 : ((245 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((159719/2500000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((79605706509/1250000000000 : ℚ) : ℝ)
      = ((159719/2500000 : ℚ) : ℝ) * ((498411/500000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c246 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((5331/8000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 2103649/10000000) (δ := 11423/1000000000) (ψ := -35361/50000) 226 198
    (log_br_246).1 (log_br_246).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t246 : ((2124164141/50000000000 : ℚ) : ℝ) ≤ stT226 246 := by
  have hc : ((26653/40000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((246 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c246).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_246).1
  have hw2 : ((246 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hq0 : (0:ℝ) ≤ ((79697/1250000 : ℚ) : ℝ) := by push_cast; norm_num
  have hkey := (mul_lower_of_bracket hw hw2 hq0 hc).1 (by push_cast; norm_num)
  calc ((2124164141/50000000000 : ℚ) : ℝ)
      = ((79697/1250000 : ℚ) : ℝ) * ((26653/40000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c247 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-186403/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 4395741/10000000) (δ := 11423/1000000000) (ψ := -35361/50000) 226 198
    (log_br_247).1 (log_br_247).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t247 : ((-23727449421/2000000000000 : ℚ) : ℝ) ≤ stT226 247 := by
  have hc : ((-186453/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((247 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c247).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_247).2
  have h0 : (0:ℝ) ≤ ((247 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-23727449421/2000000000000 : ℚ) : ℝ)
      = ((127257/2000000 : ℚ) : ℝ) * ((-186453/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c248 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-891493/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := 6678567/10000000) (δ := 11423/1000000000) (ψ := -35361/50000) 226 198
    (log_br_248).1 (log_br_248).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t248 : ((-566130696543/10000000000000 : ℚ) : ℝ) ≤ stT226 248 := by
  have hc : ((-891543/1000000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((248 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c248).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_248).2
  have h0 : (0:ℝ) ≤ ((248 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-566130696543/10000000000000 : ℚ) : ℝ)
      = ((635001/10000000 : ℚ) : ℝ) * ((-891543/1000000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c249 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-452529/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -337789/500000) (δ := 1133/100000000) (ψ := -35361/50000) 226 199
    (log_br_249).1 (log_br_249).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t249 : ((-5735895673/100000000000 : ℚ) : ℝ) ≤ stT226 249 := by
  have hc : ((-226277/250000 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((249 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c249).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_249).2
  have h0 : (0:ℝ) ≤ ((249 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-5735895673/100000000000 : ℚ) : ℝ)
      = ((25349/400000 : ℚ) : ℝ) * ((-226277/250000 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_c250 :
    |Real.cos (((226 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-111887/500000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  cosMulShift_eval (r := -1122801/2500000) (δ := 11473/1000000000) (ψ := -35361/50000) 226 199
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])

theorem st226_t250 : ((-1105928373/78125000000 : ℚ) : ℝ) ≤ stT226 250 := by
  have hc : ((-13989/62500 : ℚ) : ℝ)
      ≤ Real.cos (((226 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)) := by
    have h := (abs_le.mp st226_c250).1
    push_cast at h ⊢
    linarith
  have hw := (sq_br_250).2
  have h0 : (0:ℝ) ≤ ((250 : ℕ) : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hkey := (mul_lower_of_bracket h0 hw (le_refl (0:ℝ)) hc).2
    (by push_cast; norm_num)
  calc ((-1105928373/78125000000 : ℚ) : ℝ)
      = ((79057/1250000 : ℚ) : ℝ) * ((-13989/62500 : ℚ) : ℝ) := by
        push_cast; norm_num
    _ ≤ _ := hkey

theorem st226_p1 : ((760121/1000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 1, stT226 (i+1) := by
  rw [Finset.sum_range_one]
  exact st226_t1

theorem st226_p2 : ((3599699103177/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 2, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 2, stT226 (i+1))
      = (∑ i ∈ Finset.range 1, stT226 (i+1)) + stT226 2 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 1
    simpa using h
  have hprev := st226_p1
  have hstep := st226_t2
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p3 : ((10408364758719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 3, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 3, stT226 (i+1))
      = (∑ i ∈ Finset.range 2, stT226 (i+1)) + stT226 3 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 2
    simpa using h
  have hprev := st226_p2
  have hstep := st226_t3
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p4 : ((15352324758719/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 4, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 4, stT226 (i+1))
      = (∑ i ∈ Finset.range 3, stT226 (i+1)) + stT226 4 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 3
    simpa using h
  have hprev := st226_p3
  have hstep := st226_t4
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p5 : ((619490748997/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 5, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 5, stT226 (i+1))
      = (∑ i ∈ Finset.range 4, stT226 (i+1)) + stT226 5 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 4
    simpa using h
  have hprev := st226_p4
  have hstep := st226_t5
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p6 : ((2003917317477/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 6, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 6, stT226 (i+1))
      = (∑ i ∈ Finset.range 5, stT226 (i+1)) + stT226 6 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 5
    simpa using h
  have hprev := st226_p5
  have hstep := st226_t6
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p7 : ((297143346057/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 7, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 7, stT226 (i+1))
      = (∑ i ∈ Finset.range 6, stT226 (i+1)) + stT226 7 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 6
    simpa using h
  have hprev := st226_p6
  have hstep := st226_t7
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p8 : ((85853216607/39062500000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 8, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 8, stT226 (i+1))
      = (∑ i ∈ Finset.range 7, stT226 (i+1)) + stT226 8 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 7
    simpa using h
  have hprev := st226_p7
  have hstep := st226_t8
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p9 : ((12014234956527/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 9, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 9, stT226 (i+1))
      = (∑ i ∈ Finset.range 8, stT226 (i+1)) + stT226 9 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 8
    simpa using h
  have hprev := st226_p8
  have hstep := st226_t9
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p10 : ((26924783605969/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 10, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 10, stT226 (i+1))
      = (∑ i ∈ Finset.range 9, stT226 (i+1)) + stT226 10 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 9
    simpa using h
  have hprev := st226_p9
  have hstep := st226_t10
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p11 : ((24966575607073/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 11, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 11, stT226 (i+1))
      = (∑ i ∈ Finset.range 10, stT226 (i+1)) + stT226 11 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 10
    simpa using h
  have hprev := st226_p10
  have hstep := st226_t11
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p12 : ((22083137598369/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 12, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 12, stT226 (i+1))
      = (∑ i ∈ Finset.range 11, stT226 (i+1)) + stT226 12 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 11
    simpa using h
  have hprev := st226_p11
  have hstep := st226_t12
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p13 : ((20168401260001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 13, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 13, stT226 (i+1))
      = (∑ i ∈ Finset.range 12, stT226 (i+1)) + stT226 13 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 12
    simpa using h
  have hprev := st226_p12
  have hstep := st226_t13
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p14 : ((22769536924673/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 14, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 14, stT226 (i+1))
      = (∑ i ∈ Finset.range 13, stT226 (i+1)) + stT226 14 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 13
    simpa using h
  have hprev := st226_p13
  have hstep := st226_t14
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p15 : ((20204774955281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 15, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 15, stT226 (i+1))
      = (∑ i ∈ Finset.range 14, stT226 (i+1)) + stT226 15 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 14
    simpa using h
  have hprev := st226_p14
  have hstep := st226_t15
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p16 : ((21542224955281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 16, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 16, stT226 (i+1))
      = (∑ i ∈ Finset.range 15, stT226 (i+1)) + stT226 16 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 15
    simpa using h
  have hprev := st226_p15
  have hstep := st226_t16
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p17 : ((23947452925837/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 17, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 17, stT226 (i+1))
      = (∑ i ∈ Finset.range 16, stT226 (i+1)) + stT226 17 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 16
    simpa using h
  have hprev := st226_p16
  have hstep := st226_t17
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p18 : ((26038041873001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 18, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 18, stT226 (i+1))
      = (∑ i ∈ Finset.range 17, stT226 (i+1)) + stT226 18 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 17
    simpa using h
  have hprev := st226_p17
  have hstep := st226_t18
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p19 : ((28311890995237/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 19, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 19, stT226 (i+1))
      = (∑ i ∈ Finset.range 18, stT226 (i+1)) + stT226 19 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 18
    simpa using h
  have hprev := st226_p18
  have hstep := st226_t19
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p20 : ((931315553837/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 20, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 20, stT226 (i+1))
      = (∑ i ∈ Finset.range 19, stT226 (i+1)) + stT226 20 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 19
    simpa using h
  have hprev := st226_p19
  have hstep := st226_t20
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p21 : ((7055255437531/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 21, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 21, stT226 (i+1))
      = (∑ i ∈ Finset.range 20, stT226 (i+1)) + stT226 21 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 20
    simpa using h
  have hprev := st226_p20
  have hstep := st226_t21
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p22 : ((6908725725703/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 22, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 22, stT226 (i+1))
      = (∑ i ∈ Finset.range 21, stT226 (i+1)) + stT226 22 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 21
    simpa using h
  have hprev := st226_p21
  have hstep := st226_t22
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p23 : ((7316964601171/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 23, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 23, stT226 (i+1))
      = (∑ i ∈ Finset.range 22, stT226 (i+1)) + stT226 23 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 22
    simpa using h
  have hprev := st226_p22
  have hstep := st226_t23
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p24 : ((6863668031473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 24, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 24, stT226 (i+1))
      = (∑ i ∈ Finset.range 23, stT226 (i+1)) + stT226 24 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 23
    simpa using h
  have hprev := st226_p23
  have hstep := st226_t24
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p25 : ((7253579531473/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 25, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 25, stT226 (i+1))
      = (∑ i ∈ Finset.range 24, stT226 (i+1)) + stT226 25 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 24
    simpa using h
  have hprev := st226_p24
  have hstep := st226_t25
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p26 : ((3546514011881/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 26, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 26, stT226 (i+1))
      = (∑ i ∈ Finset.range 25, stT226 (i+1)) + stT226 26 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 25
    simpa using h
  have hprev := st226_p25
  have hstep := st226_t26
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p27 : ((27346639812697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 27, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 27, stT226 (i+1))
      = (∑ i ∈ Finset.range 26, stT226 (i+1)) + stT226 27 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 26
    simpa using h
  have hprev := st226_p26
  have hstep := st226_t27
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p28 : ((29199893756997/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 28, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 28, stT226 (i+1))
      = (∑ i ∈ Finset.range 27, stT226 (i+1)) + stT226 28 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 27
    simpa using h
  have hprev := st226_p27
  have hstep := st226_t28
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p29 : ((29422353012491/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 29, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 29, stT226 (i+1))
      = (∑ i ∈ Finset.range 28, stT226 (i+1)) + stT226 29 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 28
    simpa using h
  have hprev := st226_p28
  have hstep := st226_t29
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p30 : ((27684876509481/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 30, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 30, stT226 (i+1))
      = (∑ i ∈ Finset.range 29, stT226 (i+1)) + stT226 30 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 29
    simpa using h
  have hprev := st226_p29
  have hstep := st226_t30
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p31 : ((26452867880019/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 31, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 31, stT226 (i+1))
      = (∑ i ∈ Finset.range 30, stT226 (i+1)) + stT226 31 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 30
    simpa using h
  have hprev := st226_p30
  have hstep := st226_t31
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p32 : ((26692766100581/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 32, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 32, stT226 (i+1))
      = (∑ i ∈ Finset.range 31, stT226 (i+1)) + stT226 32 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 31
    simpa using h
  have hprev := st226_p31
  have hstep := st226_t32
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p33 : ((5590068892321/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 33, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 33, stT226 (i+1))
      = (∑ i ∈ Finset.range 32, stT226 (i+1)) + stT226 33 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 32
    simpa using h
  have hprev := st226_p32
  have hstep := st226_t33
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p34 : ((591774661731/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 34, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 34, stT226 (i+1))
      = (∑ i ∈ Finset.range 33, stT226 (i+1)) + stT226 34 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 33
    simpa using h
  have hprev := st226_p33
  have hstep := st226_t34
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p35 : ((15639049792497/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 35, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 35, stT226 (i+1))
      = (∑ i ∈ Finset.range 34, stT226 (i+1)) + stT226 35 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 34
    simpa using h
  have hprev := st226_p34
  have hstep := st226_t35
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p36 : ((2058903994953/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 36, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 36, stT226 (i+1))
      = (∑ i ∈ Finset.range 35, stT226 (i+1)) + stT226 36 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 35
    simpa using h
  have hprev := st226_p35
  have hstep := st226_t36
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p37 : ((6917018668069/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 37, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 37, stT226 (i+1))
      = (∑ i ∈ Finset.range 36, stT226 (i+1)) + stT226 37 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 36
    simpa using h
  have hprev := st226_p36
  have hstep := st226_t37
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p38 : ((36136874052893/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 38, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 38, stT226 (i+1))
      = (∑ i ∈ Finset.range 37, stT226 (i+1)) + stT226 38 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 37
    simpa using h
  have hprev := st226_p37
  have hstep := st226_t38
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p39 : ((37352909262227/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 39, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 39, stT226 (i+1))
      = (∑ i ∈ Finset.range 38, stT226 (i+1)) + stT226 39 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 38
    simpa using h
  have hprev := st226_p38
  have hstep := st226_t39
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p40 : ((1512871576463/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 40, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 40, stT226 (i+1))
      = (∑ i ∈ Finset.range 39, stT226 (i+1)) + stT226 40 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 39
    simpa using h
  have hprev := st226_p39
  have hstep := st226_t40
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p41 : ((37211338823873/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 41, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 41, stT226 (i+1))
      = (∑ i ∈ Finset.range 40, stT226 (i+1)) + stT226 41 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 40
    simpa using h
  have hprev := st226_p40
  have hstep := st226_t41
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p42 : ((35752557566341/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 42, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 42, stT226 (i+1))
      = (∑ i ∈ Finset.range 41, stT226 (i+1)) + stT226 42 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 41
    simpa using h
  have hprev := st226_p41
  have hstep := st226_t42
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p43 : ((34523090978351/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 43, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 43, stT226 (i+1))
      = (∑ i ∈ Finset.range 42, stT226 (i+1)) + stT226 43 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 42
    simpa using h
  have hprev := st226_p42
  have hstep := st226_t43
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p44 : ((34748178134487/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 44, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 44, stT226 (i+1))
      = (∑ i ∈ Finset.range 43, stT226 (i+1)) + stT226 44 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 43
    simpa using h
  have hprev := st226_p43
  have hstep := st226_t44
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p45 : ((9050999760883/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 45, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 45, stT226 (i+1))
      = (∑ i ∈ Finset.range 44, stT226 (i+1)) + stT226 45 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 44
    simpa using h
  have hprev := st226_p44
  have hstep := st226_t45
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p46 : ((18436747188269/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 46, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 46, stT226 (i+1))
      = (∑ i ∈ Finset.range 45, stT226 (i+1)) + stT226 46 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 45
    simpa using h
  have hprev := st226_p45
  have hstep := st226_t46
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p47 : ((8921442412897/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 47, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 47, stT226 (i+1))
      = (∑ i ∈ Finset.range 46, stT226 (i+1)) + stT226 47 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 46
    simpa using h
  have hprev := st226_p46
  have hstep := st226_t47
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p48 : ((8698733104537/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 48, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 48, stT226 (i+1))
      = (∑ i ∈ Finset.range 47, stT226 (i+1)) + stT226 48 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 47
    simpa using h
  have hprev := st226_p47
  have hstep := st226_t48
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p49 : ((35963610638973/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 49, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 49, stT226 (i+1))
      = (∑ i ∈ Finset.range 48, stT226 (i+1)) + stT226 49 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 48
    simpa using h
  have hprev := st226_p48
  have hstep := st226_t49
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p50 : ((18299545746581/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 50, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 50, stT226 (i+1))
      = (∑ i ∈ Finset.range 49, stT226 (i+1)) + stT226 50 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 49
    simpa using h
  have hprev := st226_p49
  have hstep := st226_t50
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p51 : ((880883175527/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 51, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 51, stT226 (i+1))
      = (∑ i ∈ Finset.range 50, stT226 (i+1)) + stT226 51 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 50
    simpa using h
  have hprev := st226_p50
  have hstep := st226_t51
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p52 : ((1768326371929/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 52, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 52, stT226 (i+1))
      = (∑ i ∈ Finset.range 51, stT226 (i+1)) + stT226 52 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 51
    simpa using h
  have hprev := st226_p51
  have hstep := st226_t52
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p53 : ((457129916519/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 53, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 53, stT226 (i+1))
      = (∑ i ∈ Finset.range 52, stT226 (i+1)) + stT226 53 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 52
    simpa using h
  have hprev := st226_p52
  have hstep := st226_t53
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p54 : ((1771621746361/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 54, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 54, stT226 (i+1))
      = (∑ i ∈ Finset.range 53, stT226 (i+1)) + stT226 54 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 53
    simpa using h
  have hprev := st226_p53
  have hstep := st226_t54
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p55 : ((1770604985341/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 55, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 55, stT226 (i+1))
      = (∑ i ∈ Finset.range 54, stT226 (i+1)) + stT226 55 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 54
    simpa using h
  have hprev := st226_p54
  have hstep := st226_t55
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p56 : ((912389749367/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 56, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 56, stT226 (i+1))
      = (∑ i ∈ Finset.range 55, stT226 (i+1)) + stT226 56 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 55
    simpa using h
  have hprev := st226_p55
  have hstep := st226_t56
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p57 : ((35206886916863/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 57, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 57, stT226 (i+1))
      = (∑ i ∈ Finset.range 56, stT226 (i+1)) + stT226 57 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 56
    simpa using h
  have hprev := st226_p56
  have hstep := st226_t57
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p58 : ((35891464650839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 58, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 58, stT226 (i+1))
      = (∑ i ∈ Finset.range 57, stT226 (i+1)) + stT226 58 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 57
    simpa using h
  have hprev := st226_p57
  have hstep := st226_t58
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p59 : ((9028953168191/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 59, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 59, stT226 (i+1))
      = (∑ i ∈ Finset.range 58, stT226 (i+1)) + stT226 59 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 58
    simpa using h
  have hprev := st226_p58
  have hstep := st226_t59
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p60 : ((8790759426711/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 60, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 60, stT226 (i+1))
      = (∑ i ∈ Finset.range 59, stT226 (i+1)) + stT226 60 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 59
    simpa using h
  have hprev := st226_p59
  have hstep := st226_t60
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p61 : ((1821479334751/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 61, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 61, stT226 (i+1))
      = (∑ i ∈ Finset.range 60, stT226 (i+1)) + stT226 61 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 60
    simpa using h
  have hprev := st226_p60
  have hstep := st226_t61
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p62 : ((14101293857/4000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 62, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 62, stT226 (i+1))
      = (∑ i ∈ Finset.range 61, stT226 (i+1)) + stT226 62 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 61
    simpa using h
  have hprev := st226_p61
  have hstep := st226_t62
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p63 : ((18037075212121/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 63, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 63, stT226 (i+1))
      = (∑ i ∈ Finset.range 62, stT226 (i+1)) + stT226 63 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 62
    simpa using h
  have hprev := st226_p62
  have hstep := st226_t63
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p64 : ((17857000068061/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 64, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 64, stT226 (i+1))
      = (∑ i ∈ Finset.range 63, stT226 (i+1)) + stT226 64 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 63
    simpa using h
  have hprev := st226_p63
  have hstep := st226_t64
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p65 : ((142508013471/40000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 65, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 65, stT226 (i+1))
      = (∑ i ∈ Finset.range 64, stT226 (i+1)) + stT226 65 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 64
    simpa using h
  have hprev := st226_p64
  have hstep := st226_t65
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p66 : ((563787168299/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 66, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 66, stT226 (i+1))
      = (∑ i ∈ Finset.range 65, stT226 (i+1)) + stT226 66 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 65
    simpa using h
  have hprev := st226_p65
  have hstep := st226_t66
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p67 : ((35356671172321/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 67, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 67, stT226 (i+1))
      = (∑ i ∈ Finset.range 66, stT226 (i+1)) + stT226 67 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 66
    simpa using h
  have hprev := st226_p66
  have hstep := st226_t67
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p68 : ((36261725506027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 68, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 68, stT226 (i+1))
      = (∑ i ∈ Finset.range 67, stT226 (i+1)) + stT226 68 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 67
    simpa using h
  have hprev := st226_p67
  have hstep := st226_t68
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p69 : ((704968675483/200000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 69, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 69, stT226 (i+1))
      = (∑ i ∈ Finset.range 68, stT226 (i+1)) + stT226 69 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 68
    simpa using h
  have hprev := st226_p68
  have hstep := st226_t69
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p70 : ((18159625843429/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 70, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 70, stT226 (i+1))
      = (∑ i ∈ Finset.range 69, stT226 (i+1)) + stT226 70 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 69
    simpa using h
  have hprev := st226_p69
  have hstep := st226_t70
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p71 : ((4403036227927/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 71, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 71, stT226 (i+1))
      = (∑ i ∈ Finset.range 70, stT226 (i+1)) + stT226 71 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 70
    simpa using h
  have hprev := st226_p70
  have hstep := st226_t71
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p72 : ((7264015991563/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 72, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 72, stT226 (i+1))
      = (∑ i ∈ Finset.range 71, stT226 (i+1)) + stT226 72 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 71
    simpa using h
  have hprev := st226_p71
  have hstep := st226_t72
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p73 : ((35242490992711/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 73, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 73, stT226 (i+1))
      = (∑ i ∈ Finset.range 72, stT226 (i+1)) + stT226 73 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 72
    simpa using h
  have hprev := st226_p72
  have hstep := st226_t73
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p74 : ((36280014772423/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 74, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 74, stT226 (i+1))
      = (∑ i ∈ Finset.range 73, stT226 (i+1)) + stT226 74 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 73
    simpa using h
  have hprev := st226_p73
  have hstep := st226_t74
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p75 : ((17655713662451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 75, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 75, stT226 (i+1))
      = (∑ i ∈ Finset.range 74, stT226 (i+1)) + stT226 75 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 74
    simpa using h
  have hprev := st226_p74
  have hstep := st226_t75
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p76 : ((9042688768303/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 76, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 76, stT226 (i+1))
      = (∑ i ∈ Finset.range 75, stT226 (i+1)) + stT226 76 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 75
    simpa using h
  have hprev := st226_p75
  have hstep := st226_t76
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p77 : ((17736197129979/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 77, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 77, stT226 (i+1))
      = (∑ i ∈ Finset.range 76, stT226 (i+1)) + stT226 77 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 76
    simpa using h
  have hprev := st226_p76
  have hstep := st226_t77
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p78 : ((35948590336463/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 78, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 78, stT226 (i+1))
      = (∑ i ∈ Finset.range 77, stT226 (i+1)) + stT226 78 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 77
    simpa using h
  have hprev := st226_p77
  have hstep := st226_t78
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p79 : ((35756477060111/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 79, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 79, stT226 (i+1))
      = (∑ i ∈ Finset.range 78, stT226 (i+1)) + stT226 79 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 78
    simpa using h
  have hprev := st226_p78
  have hstep := st226_t79
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p80 : ((35614547115947/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 80, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 80, stT226 (i+1))
      = (∑ i ∈ Finset.range 79, stT226 (i+1)) + stT226 80 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 79
    simpa using h
  have hprev := st226_p79
  have hstep := st226_t80
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p81 : ((18054554088801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 81, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 81, stT226 (i+1))
      = (∑ i ∈ Finset.range 80, stT226 (i+1)) + stT226 81 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 80
    simpa using h
  have hprev := st226_p80
  have hstep := st226_t81
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p82 : ((3529422014941/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 82, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 82, stT226 (i+1))
      = (∑ i ∈ Finset.range 81, stT226 (i+1)) + stT226 82 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 81
    simpa using h
  have hprev := st226_p81
  have hstep := st226_t82
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p83 : ((567647368209/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 83, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 83, stT226 (i+1))
      = (∑ i ∈ Finset.range 82, stT226 (i+1)) + stT226 83 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 82
    simpa using h
  have hprev := st226_p82
  have hstep := st226_t83
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p84 : ((17621667742153/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 84, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 84, stT226 (i+1))
      = (∑ i ∈ Finset.range 83, stT226 (i+1)) + stT226 84 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 83
    simpa using h
  have hprev := st226_p83
  have hstep := st226_t84
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p85 : ((18080191359329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 85, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 85, stT226 (i+1))
      = (∑ i ∈ Finset.range 84, stT226 (i+1)) + stT226 85 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 84
    simpa using h
  have hprev := st226_p84
  have hstep := st226_t85
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p86 : ((17817308472029/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 86, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 86, stT226 (i+1))
      = (∑ i ∈ Finset.range 85, stT226 (i+1)) + stT226 86 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 85
    simpa using h
  have hprev := st226_p85
  have hstep := st226_t86
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p87 : ((35613576726433/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 87, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 87, stT226 (i+1))
      = (∑ i ∈ Finset.range 86, stT226 (i+1)) + stT226 87 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 86
    simpa using h
  have hprev := st226_p86
  have hstep := st226_t87
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p88 : ((9049046702011/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 88, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 88, stT226 (i+1))
      = (∑ i ∈ Finset.range 87, stT226 (i+1)) + stT226 88 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 87
    simpa using h
  have hprev := st226_p87
  have hstep := st226_t88
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p89 : ((17610861613329/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 89, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 89, stT226 (i+1))
      = (∑ i ∈ Finset.range 88, stT226 (i+1)) + stT226 89 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 88
    simpa using h
  have hprev := st226_p88
  have hstep := st226_t89
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p90 : ((18126101782929/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 90, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 90, stT226 (i+1))
      = (∑ i ∈ Finset.range 89, stT226 (i+1)) + stT226 90 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 89
    simpa using h
  have hprev := st226_p89
  have hstep := st226_t90
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p91 : ((17782576691859/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 91, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 91, stT226 (i+1))
      = (∑ i ∈ Finset.range 90, stT226 (i+1)) + stT226 91 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 90
    simpa using h
  have hprev := st226_p90
  have hstep := st226_t91
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p92 : ((17804971138419/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 92, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 92, stT226 (i+1))
      = (∑ i ∈ Finset.range 91, stT226 (i+1)) + stT226 92 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 91
    simpa using h
  have hprev := st226_p91
  have hstep := st226_t92
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p93 : ((3624181044259/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 93, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 93, stT226 (i+1))
      = (∑ i ∈ Finset.range 92, stT226 (i+1)) + stT226 93 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 92
    simpa using h
  have hprev := st226_p92
  have hstep := st226_t93
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p94 : ((17614550250257/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 94, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 94, stT226 (i+1))
      = (∑ i ∈ Finset.range 93, stT226 (i+1)) + stT226 94 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 93
    simpa using h
  have hprev := st226_p93
  have hstep := st226_t94
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p95 : ((4512357245043/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 95, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 95, stT226 (i+1))
      = (∑ i ∈ Finset.range 94, stT226 (i+1)) + stT226 95 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 94
    simpa using h
  have hprev := st226_p94
  have hstep := st226_t95
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p96 : ((35859460077963/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 96, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 96, stT226 (i+1))
      = (∑ i ∈ Finset.range 95, stT226 (i+1)) + stT226 96 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 95
    simpa using h
  have hprev := st226_p95
  have hstep := st226_t96
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p97 : ((35317591721697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 97, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 97, stT226 (i+1))
      = (∑ i ∈ Finset.range 96, stT226 (i+1)) + stT226 97 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 96
    simpa using h
  have hprev := st226_p96
  have hstep := st226_t97
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p98 : ((36310588310281/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 98, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 98, stT226 (i+1))
      = (∑ i ∈ Finset.range 97, stT226 (i+1)) + stT226 98 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 97
    simpa using h
  have hprev := st226_p97
  have hstep := st226_t98
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p99 : ((35518332935489/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 99, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 99, stT226 (i+1))
      = (∑ i ∈ Finset.range 98, stT226 (i+1)) + stT226 99 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 98
    simpa using h
  have hprev := st226_p98
  have hstep := st226_t99
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p100 : ((35555982897839/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 100, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 100, stT226 (i+1))
      = (∑ i ∈ Finset.range 99, stT226 (i+1)) + stT226 100 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 99
    simpa using h
  have hprev := st226_p99
  have hstep := st226_t100
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p101 : ((36306819907373/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 101, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 101, stT226 (i+1))
      = (∑ i ∈ Finset.range 100, stT226 (i+1)) + stT226 101 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 100
    simpa using h
  have hprev := st226_p100
  have hstep := st226_t101
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p102 : ((7067243287749/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 102, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 102, stT226 (i+1))
      = (∑ i ∈ Finset.range 101, stT226 (i+1)) + stT226 102 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 101
    simpa using h
  have hprev := st226_p101
  have hstep := st226_t102
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p103 : ((2234451759099/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 103, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 103, stT226 (i+1))
      = (∑ i ∈ Finset.range 102, stT226 (i+1)) + stT226 103 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 102
    simpa using h
  have hprev := st226_p102
  have hstep := st226_t103
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p104 : ((1132535062227/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 104, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 104, stT226 (i+1))
      = (∑ i ∈ Finset.range 103, stT226 (i+1)) + stT226 104 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 103
    simpa using h
  have hprev := st226_p103
  have hstep := st226_t104
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p105 : ((17633737661287/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 105, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 105, stT226 (i+1))
      = (∑ i ∈ Finset.range 104, stT226 (i+1)) + stT226 105 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 104
    simpa using h
  have hprev := st226_p104
  have hstep := st226_t105
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p106 : ((4480944968533/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 106, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 106, stT226 (i+1))
      = (∑ i ∈ Finset.range 105, stT226 (i+1)) + stT226 106 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 105
    simpa using h
  have hprev := st226_p105
  have hstep := st226_t106
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p107 : ((4525693002817/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 107, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 107, stT226 (i+1))
      = (∑ i ∈ Finset.range 106, stT226 (i+1)) + stT226 107 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 106
    simpa using h
  have hprev := st226_p106
  have hstep := st226_t107
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p108 : ((881359068951/250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 108, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 108, stT226 (i+1))
      = (∑ i ∈ Finset.range 107, stT226 (i+1)) + stT226 108 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 107
    simpa using h
  have hprev := st226_p107
  have hstep := st226_t108
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p109 : ((17922416397217/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 109, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 109, stT226 (i+1))
      = (∑ i ∈ Finset.range 108, stT226 (i+1)) + stT226 109 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 108
    simpa using h
  have hprev := st226_p108
  have hstep := st226_t109
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p110 : ((9056939358891/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 110, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 110, stT226 (i+1))
      = (∑ i ∈ Finset.range 109, stT226 (i+1)) + stT226 110 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 109
    simpa using h
  have hprev := st226_p109
  have hstep := st226_t110
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p111 : ((17640162976983/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 111, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 111, stT226 (i+1))
      = (∑ i ∈ Finset.range 110, stT226 (i+1)) + stT226 111 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 110
    simpa using h
  have hprev := st226_p110
  have hstep := st226_t111
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p112 : ((1117110419321/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 112, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 112, stT226 (i+1))
      = (∑ i ∈ Finset.range 111, stT226 (i+1)) + stT226 112 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 111
    simpa using h
  have hprev := st226_p111
  have hstep := st226_t112
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p113 : ((2268160546367/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 113, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 113, stT226 (i+1))
      = (∑ i ∈ Finset.range 112, stT226 (i+1)) + stT226 113 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 112
    simpa using h
  have hprev := st226_p112
  have hstep := st226_t113
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p114 : ((17685845386687/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 114, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 114, stT226 (i+1))
      = (∑ i ∈ Finset.range 113, stT226 (i+1)) + stT226 114 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 113
    simpa using h
  have hprev := st226_p113
  have hstep := st226_t114
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p115 : ((17782102179583/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 115, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 115, stT226 (i+1))
      = (∑ i ∈ Finset.range 114, stT226 (i+1)) + stT226 115 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 114
    simpa using h
  have hprev := st226_p114
  have hstep := st226_t115
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p116 : ((18166821316801/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 116, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 116, stT226 (i+1))
      = (∑ i ∈ Finset.range 115, stT226 (i+1)) + stT226 116 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 115
    simpa using h
  have hprev := st226_p115
  have hstep := st226_t116
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p117 : ((277926876997/78125000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 117, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 117, stT226 (i+1))
      = (∑ i ∈ Finset.range 116, stT226 (i+1)) + stT226 117 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 116
    simpa using h
  have hprev := st226_p116
  have hstep := st226_t117
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p118 : ((35342271475841/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 118, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 118, stT226 (i+1))
      = (∑ i ∈ Finset.range 117, stT226 (i+1)) + stT226 118 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 117
    simpa using h
  have hprev := st226_p117
  have hstep := st226_t118
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p119 : ((36255899454239/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 119, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 119, stT226 (i+1))
      = (∑ i ∈ Finset.range 118, stT226 (i+1)) + stT226 119 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 118
    simpa using h
  have hprev := st226_p118
  have hstep := st226_t119
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p120 : ((8974736930737/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 120, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 120, stT226 (i+1))
      = (∑ i ∈ Finset.range 119, stT226 (i+1)) + stT226 120 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 119
    simpa using h
  have hprev := st226_p119
  have hstep := st226_t120
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p121 : ((35207364926517/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 121, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 121, stT226 (i+1))
      = (∑ i ∈ Finset.range 120, stT226 (i+1)) + stT226 121 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 120
    simpa using h
  have hprev := st226_p120
  have hstep := st226_t121
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p122 : ((35967048174503/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 122, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 122, stT226 (i+1))
      = (∑ i ∈ Finset.range 121, stT226 (i+1)) + stT226 122 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 121
    simpa using h
  have hprev := st226_p121
  have hstep := st226_t122
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p123 : ((7246860212553/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 123, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 123, stT226 (i+1))
      = (∑ i ∈ Finset.range 122, stT226 (i+1)) + stT226 123 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 122
    simpa using h
  have hprev := st226_p122
  have hstep := st226_t123
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p124 : ((35337014037013/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 124, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 124, stT226 (i+1))
      = (∑ i ∈ Finset.range 123, stT226 (i+1)) + stT226 124 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 123
    simpa using h
  have hprev := st226_p123
  have hstep := st226_t124
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p125 : ((7103402778611/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 125, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 125, stT226 (i+1))
      = (∑ i ∈ Finset.range 124, stT226 (i+1)) + stT226 125 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 124
    simpa using h
  have hprev := st226_p124
  have hstep := st226_t125
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p126 : ((7265146997723/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 126, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 126, stT226 (i+1))
      = (∑ i ∈ Finset.range 125, stT226 (i+1)) + stT226 126 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 125
    simpa using h
  have hprev := st226_p125
  have hstep := st226_t126
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p127 : ((3578976692383/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 127, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 127, stT226 (i+1))
      = (∑ i ∈ Finset.range 126, stT226 (i+1)) + stT226 127 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 126
    simpa using h
  have hprev := st226_p126
  have hstep := st226_t127
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p128 : ((17603260078259/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 128, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 128, stT226 (i+1))
      = (∑ i ∈ Finset.range 127, stT226 (i+1)) + stT226 128 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 127
    simpa using h
  have hprev := st226_p127
  have hstep := st226_t128
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p129 : ((17982488382709/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 129, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 129, stT226 (i+1))
      = (∑ i ∈ Finset.range 128, stT226 (i+1)) + stT226 129 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 128
    simpa using h
  have hprev := st226_p128
  have hstep := st226_t129
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p130 : ((9068108896681/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 130, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 130, stT226 (i+1))
      = (∑ i ∈ Finset.range 129, stT226 (i+1)) + stT226 130 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 129
    simpa using h
  have hprev := st226_p129
  have hstep := st226_t130
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p131 : ((35415620178079/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 131, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 131, stT226 (i+1))
      = (∑ i ∈ Finset.range 130, stT226 (i+1)) + stT226 131 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 130
    simpa using h
  have hprev := st226_p130
  have hstep := st226_t131
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p132 : ((4421579284567/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 132, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 132, stT226 (i+1))
      = (∑ i ∈ Finset.range 131, stT226 (i+1)) + stT226 132 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 131
    simpa using h
  have hprev := st226_p131
  have hstep := st226_t132
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p133 : ((45295664381/12500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 133, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 133, stT226 (i+1))
      = (∑ i ∈ Finset.range 132, stT226 (i+1)) + stT226 133 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 132
    simpa using h
  have hprev := st226_p132
  have hstep := st226_t133
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p134 : ((18029215544273/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 134, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 134, stT226 (i+1))
      = (∑ i ∈ Finset.range 133, stT226 (i+1)) + stT226 134 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 133
    simpa using h
  have hprev := st226_p133
  have hstep := st226_t134
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p135 : ((28192508793/8000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 135, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 135, stT226 (i+1))
      = (∑ i ∈ Finset.range 134, stT226 (i+1)) + stT226 135 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 134
    simpa using h
  have hprev := st226_p134
  have hstep := st226_t135
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p136 : ((3558570792189/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 136, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 136, stT226 (i+1))
      = (∑ i ∈ Finset.range 135, stT226 (i+1)) + stT226 136 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 135
    simpa using h
  have hprev := st226_p135
  have hstep := st226_t136
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p137 : ((18167897888091/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 137, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 137, stT226 (i+1))
      = (∑ i ∈ Finset.range 136, stT226 (i+1)) + stT226 137 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 136
    simpa using h
  have hprev := st226_p136
  have hstep := st226_t137
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p138 : ((8968747908607/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 138, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 138, stT226 (i+1))
      = (∑ i ∈ Finset.range 137, stT226 (i+1)) + stT226 138 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 137
    simpa using h
  have hprev := st226_p137
  have hstep := st226_t138
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p139 : ((3519106121979/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 139, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 139, stT226 (i+1))
      = (∑ i ∈ Finset.range 138, stT226 (i+1)) + stT226 139 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 138
    simpa using h
  have hprev := st226_p138
  have hstep := st226_t139
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p140 : ((17861953576239/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 140, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 140, stT226 (i+1))
      = (∑ i ∈ Finset.range 139, stT226 (i+1)) + stT226 140 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 139
    simpa using h
  have hprev := st226_p139
  have hstep := st226_t140
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p141 : ((36357020273409/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 141, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 141, stT226 (i+1))
      = (∑ i ∈ Finset.range 140, stT226 (i+1)) + stT226 141 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 140
    simpa using h
  have hprev := st226_p140
  have hstep := st226_t141
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p142 : ((35787203107679/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 142, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 142, stT226 (i+1))
      = (∑ i ∈ Finset.range 141, stT226 (i+1)) + stT226 142 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 141
    simpa using h
  have hprev := st226_p141
  have hstep := st226_t142
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p143 : ((2198869135827/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 143, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 143, stT226 (i+1))
      = (∑ i ∈ Finset.range 142, stT226 (i+1)) + stT226 143 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 142
    simpa using h
  have hprev := st226_p142
  have hstep := st226_t143
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p144 : ((35759363442249/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 144, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 144, stT226 (i+1))
      = (∑ i ∈ Finset.range 143, stT226 (i+1)) + stT226 144 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 143
    simpa using h
  have hprev := st226_p143
  have hstep := st226_t144
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p145 : ((7272381363207/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 145, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 145, stT226 (i+1))
      = (∑ i ∈ Finset.range 144, stT226 (i+1)) + stT226 145 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 144
    simpa using h
  have hprev := st226_p144
  have hstep := st226_t145
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p146 : ((35802992207601/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 146, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 146, stT226 (i+1))
      = (∑ i ∈ Finset.range 145, stT226 (i+1)) + stT226 146 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 145
    simpa using h
  have hprev := st226_p145
  have hstep := st226_t146
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p147 : ((3517919507727/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 147, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 147, stT226 (i+1))
      = (∑ i ∈ Finset.range 146, stT226 (i+1)) + stT226 147 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 146
    simpa using h
  have hprev := st226_p146
  have hstep := st226_t147
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p148 : ((17846289002961/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 148, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 148, stT226 (i+1))
      = (∑ i ∈ Finset.range 147, stT226 (i+1)) + stT226 148 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 147
    simpa using h
  have hprev := st226_p147
  have hstep := st226_t148
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p149 : ((18178274173401/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 149, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 149, stT226 (i+1))
      = (∑ i ∈ Finset.range 148, stT226 (i+1)) + stT226 149 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 148
    simpa using h
  have hprev := st226_p148
  have hstep := st226_t149
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p150 : ((1795910759917/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 150, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 150, stT226 (i+1))
      = (∑ i ∈ Finset.range 149, stT226 (i+1)) + stT226 150 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 149
    simpa using h
  have hprev := st226_p149
  have hstep := st226_t150
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p151 : ((440038014367/125000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 151, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 151, stT226 (i+1))
      = (∑ i ∈ Finset.range 150, stT226 (i+1)) + stT226 151 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 150
    simpa using h
  have hprev := st226_p150
  have hstep := st226_t151
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p152 : ((17766305883907/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 152, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 152, stT226 (i+1))
      = (∑ i ∈ Finset.range 151, stT226 (i+1)) + stT226 152 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 151
    simpa using h
  have hprev := st226_p151
  have hstep := st226_t152
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p153 : ((18148745719411/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 153, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 153, stT226 (i+1))
      = (∑ i ∈ Finset.range 152, stT226 (i+1)) + stT226 153 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 152
    simpa using h
  have hprev := st226_p152
  have hstep := st226_t153
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p154 : ((1128525454229/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 154, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 154, stT226 (i+1))
      = (∑ i ∈ Finset.range 153, stT226 (i+1)) + stT226 154 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 153
    simpa using h
  have hprev := st226_p153
  have hstep := st226_t154
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p155 : ((4414454946131/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 155, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 155, stT226 (i+1))
      = (∑ i ∈ Finset.range 154, stT226 (i+1)) + stT226 155 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 154
    simpa using h
  have hprev := st226_p154
  have hstep := st226_t155
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p156 : ((4415026102691/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 156, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 156, stT226 (i+1))
      = (∑ i ∈ Finset.range 155, stT226 (i+1)) + stT226 156 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 155
    simpa using h
  have hprev := st226_p155
  have hstep := st226_t156
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p157 : ((18056212449499/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 157, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 157, stT226 (i+1))
      = (∑ i ∈ Finset.range 156, stT226 (i+1)) + stT226 157 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 156
    simpa using h
  have hprev := st226_p156
  have hstep := st226_t157
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p158 : ((36314462168047/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 158, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 158, stT226 (i+1))
      = (∑ i ∈ Finset.range 157, stT226 (i+1)) + stT226 158 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 157
    simpa using h
  have hprev := st226_p157
  have hstep := st226_t158
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p159 : ((35584510936531/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 159, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 159, stT226 (i+1))
      = (∑ i ∈ Finset.range 158, stT226 (i+1)) + stT226 159 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 158
    simpa using h
  have hprev := st226_p158
  have hstep := st226_t159
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p160 : ((35167479727541/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 160, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 160, stT226 (i+1))
      = (∑ i ∈ Finset.range 159, stT226 (i+1)) + stT226 160 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 159
    simpa using h
  have hprev := st226_p159
  have hstep := st226_t160
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p161 : ((35760824103241/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 161, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 161, stT226 (i+1))
      = (∑ i ∈ Finset.range 160, stT226 (i+1)) + stT226 161 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 160
    simpa using h
  have hprev := st226_p160
  have hstep := st226_t161
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p162 : ((1454846715163/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 162, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 162, stT226 (i+1))
      = (∑ i ∈ Finset.range 161, stT226 (i+1)) + stT226 162 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 161
    simpa using h
  have hprev := st226_p161
  have hstep := st226_t162
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p163 : ((17997439556141/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 163, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 163, stT226 (i+1))
      = (∑ i ∈ Finset.range 162, stT226 (i+1)) + stT226 163 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 162
    simpa using h
  have hprev := st226_p162
  have hstep := st226_t163
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p164 : ((3525179792493/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 164, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 164, stT226 (i+1))
      = (∑ i ∈ Finset.range 163, stT226 (i+1)) + stT226 164 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 163
    simpa using h
  have hprev := st226_p163
  have hstep := st226_t164
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p165 : ((17670773144181/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 165, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 165, stT226 (i+1))
      = (∑ i ∈ Finset.range 164, stT226 (i+1)) + stT226 165 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 164
    simpa using h
  have hprev := st226_p164
  have hstep := st226_t165
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p166 : ((9028635309653/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 166, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 166, stT226 (i+1))
      = (∑ i ∈ Finset.range 165, stT226 (i+1)) + stT226 166 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 165
    simpa using h
  have hprev := st226_p165
  have hstep := st226_t166
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p167 : ((36345446152697/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 167, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 167, stT226 (i+1))
      = (∑ i ∈ Finset.range 166, stT226 (i+1)) + stT226 167 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 166
    simpa using h
  have hprev := st226_p166
  have hstep := st226_t167
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p168 : ((1427105890763/400000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 168, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 168, stT226 (i+1))
      = (∑ i ∈ Finset.range 167, stT226 (i+1)) + stT226 168 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 167
    simpa using h
  have hprev := st226_p167
  have hstep := st226_t168
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p169 : ((35150940957217/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 169, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 169, stT226 (i+1))
      = (∑ i ∈ Finset.range 168, stT226 (i+1)) + stT226 169 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 168
    simpa using h
  have hprev := st226_p168
  have hstep := st226_t169
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p170 : ((35570693451741/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 170, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 170, stT226 (i+1))
      = (∑ i ∈ Finset.range 169, stT226 (i+1)) + stT226 170 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 169
    simpa using h
  have hprev := st226_p169
  have hstep := st226_t170
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p171 : ((1814656977507/500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 171, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 171, stT226 (i+1))
      = (∑ i ∈ Finset.range 170, stT226 (i+1)) + stT226 171 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 170
    simpa using h
  have hprev := st226_p170
  have hstep := st226_t171
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p172 : ((36231492753583/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 172, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 172, stT226 (i+1))
      = (∑ i ∈ Finset.range 171, stT226 (i+1)) + stT226 172 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 171
    simpa using h
  have hprev := st226_p171
  have hstep := st226_t172
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p173 : ((35483419987887/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 173, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 173, stT226 (i+1))
      = (∑ i ∈ Finset.range 172, stT226 (i+1)) + stT226 173 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 172
    simpa using h
  have hprev := st226_p172
  have hstep := st226_t173
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p174 : ((35155025146869/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 174, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 174, stT226 (i+1))
      = (∑ i ∈ Finset.range 173, stT226 (i+1)) + stT226 174 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 173
    simpa using h
  have hprev := st226_p173
  have hstep := st226_t174
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p175 : ((7144297772961/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 175, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 175, stT226 (i+1))
      = (∑ i ∈ Finset.range 174, stT226 (i+1)) + stT226 175 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 174
    simpa using h
  have hprev := st226_p174
  have hstep := st226_t175
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p176 : ((36358435797473/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 176, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 176, stT226 (i+1))
      = (∑ i ∈ Finset.range 175, stT226 (i+1)) + stT226 176 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 175
    simpa using h
  have hprev := st226_p175
  have hstep := st226_t176
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p177 : ((36155158879499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 177, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 177, stT226 (i+1))
      = (∑ i ∈ Finset.range 176, stT226 (i+1)) + stT226 177 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 176
    simpa using h
  have hprev := st226_p176
  have hstep := st226_t177
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p178 : ((35405800770923/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 178, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 178, stT226 (i+1))
      = (∑ i ∈ Finset.range 177, stT226 (i+1)) + stT226 178 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 177
    simpa using h
  have hprev := st226_p177
  have hstep := st226_t178
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p179 : ((35164669695527/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 179, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 179, stT226 (i+1))
      = (∑ i ∈ Finset.range 178, stT226 (i+1)) + stT226 179 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 178
    simpa using h
  have hprev := st226_p178
  have hstep := st226_t179
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p180 : ((35762396702807/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 180, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 180, stT226 (i+1))
      = (∑ i ∈ Finset.range 179, stT226 (i+1)) + stT226 180 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 179
    simpa using h
  have hprev := st226_p179
  have hstep := st226_t180
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p181 : ((36370788788159/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 181, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 181, stT226 (i+1))
      = (∑ i ∈ Finset.range 180, stT226 (i+1)) + stT226 181 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 180
    simpa using h
  have hprev := st226_p180
  have hstep := st226_t181
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p182 : ((36161437550659/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 182, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 182, stT226 (i+1))
      = (∑ i ∈ Finset.range 181, stT226 (i+1)) + stT226 182 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 181
    simpa using h
  have hprev := st226_p181
  have hstep := st226_t182
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p183 : ((35422965860989/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 183, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 183, stT226 (i+1))
      = (∑ i ∈ Finset.range 182, stT226 (i+1)) + stT226 183 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 182
    simpa using h
  have hprev := st226_p182
  have hstep := st226_t183
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p184 : ((35145829454529/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 184, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 184, stT226 (i+1))
      = (∑ i ∈ Finset.range 183, stT226 (i+1)) + stT226 184 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 183
    simpa using h
  have hprev := st226_p183
  have hstep := st226_t184
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p185 : ((35693069085507/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 185, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 185, stT226 (i+1))
      = (∑ i ∈ Finset.range 184, stT226 (i+1)) + stT226 185 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 184
    simpa using h
  have hprev := st226_p184
  have hstep := st226_t185
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p186 : ((36340978995027/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 186, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 186, stT226 (i+1))
      = (∑ i ∈ Finset.range 185, stT226 (i+1)) + stT226 186 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 185
    simpa using h
  have hprev := st226_p185
  have hstep := st226_t186
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p187 : ((36247493054707/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 187, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 187, stT226 (i+1))
      = (∑ i ∈ Finset.range 186, stT226 (i+1)) + stT226 187 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 186
    simpa using h
  have hprev := st226_p186
  have hstep := st226_t187
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p188 : ((8884643824383/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 188, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 188, stT226 (i+1))
      = (∑ i ∈ Finset.range 187, stT226 (i+1)) + stT226 188 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 187
    simpa using h
  have hprev := st226_p187
  have hstep := st226_t188
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p189 : ((8780582981803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 189, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 189, stT226 (i+1))
      = (∑ i ∈ Finset.range 188, stT226 (i+1)) + stT226 189 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 188
    simpa using h
  have hprev := st226_p188
  have hstep := st226_t189
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p190 : ((4440244050197/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 190, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 190, stT226 (i+1))
      = (∑ i ∈ Finset.range 189, stT226 (i+1)) + stT226 190 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 189
    simpa using h
  have hprev := st226_p189
  have hstep := st226_t190
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p191 : ((18115605244993/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 191, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 191, stT226 (i+1))
      = (∑ i ∈ Finset.range 190, stT226 (i+1)) + stT226 191 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 190
    simpa using h
  have hprev := st226_p190
  have hstep := st226_t191
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p192 : ((36368640623709/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 192, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 192, stT226 (i+1))
      = (∑ i ∈ Finset.range 191, stT226 (i+1)) + stT226 192 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 191
    simpa using h
  have hprev := st226_p191
  have hstep := st226_t192
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p193 : ((35769848727421/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 193, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 193, stT226 (i+1))
      = (∑ i ∈ Finset.range 192, stT226 (i+1)) + stT226 193 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 192
    simpa using h
  have hprev := st226_p192
  have hstep := st226_t193
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p194 : ((17584544318311/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 194, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 194, stT226 (i+1))
      = (∑ i ∈ Finset.range 193, stT226 (i+1)) + stT226 194 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 193
    simpa using h
  have hprev := st226_p193
  have hstep := st226_t194
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p195 : ((17645352422507/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 195, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 195, stT226 (i+1))
      = (∑ i ∈ Finset.range 194, stT226 (i+1)) + stT226 195 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 194
    simpa using h
  have hprev := st226_p194
  have hstep := st226_t195
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p196 : ((35983783437649/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 196, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 196, stT226 (i+1))
      = (∑ i ∈ Finset.range 195, stT226 (i+1)) + stT226 196 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 195
    simpa using h
  have hprev := st226_p195
  have hstep := st226_t196
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p197 : ((36423236358589/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 197, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 197, stT226 (i+1))
      = (∑ i ∈ Finset.range 196, stT226 (i+1)) + stT226 197 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 196
    simpa using h
  have hprev := st226_p196
  have hstep := st226_t197
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p198 : ((36095300529769/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 198, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 198, stT226 (i+1))
      = (∑ i ∈ Finset.range 197, stT226 (i+1)) + stT226 198 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 197
    simpa using h
  have hprev := st226_p197
  have hstep := st226_t198
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p199 : ((35387176324627/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 199, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 199, stT226 (i+1))
      = (∑ i ∈ Finset.range 198, stT226 (i+1)) + stT226 199 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 198
    simpa using h
  have hprev := st226_p198
  have hstep := st226_t199
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p200 : ((8779469539803/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 200, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 200, stT226 (i+1))
      = (∑ i ∈ Finset.range 199, stT226 (i+1)) + stT226 200 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 199
    simpa using h
  have hprev := st226_p199
  have hstep := st226_t200
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p201 : ((8897911072203/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 201, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 201, stT226 (i+1))
      = (∑ i ∈ Finset.range 200, stT226 (i+1)) + stT226 201 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 200
    simpa using h
  have hprev := st226_p200
  have hstep := st226_t201
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p202 : ((18133182130369/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 202, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 202, stT226 (i+1))
      = (∑ i ∈ Finset.range 201, stT226 (i+1)) + stT226 202 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 201
    simpa using h
  have hprev := st226_p201
  have hstep := st226_t202
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p203 : ((18191645129383/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 203, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 203, stT226 (i+1))
      = (∑ i ∈ Finset.range 202, stT226 (i+1)) + stT226 203 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 202
    simpa using h
  have hprev := st226_p202
  have hstep := st226_t203
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p204 : ((35816557625611/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 204, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 204, stT226 (i+1))
      = (∑ i ∈ Finset.range 203, stT226 (i+1)) + stT226 204 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 203
    simpa using h
  have hprev := st226_p203
  have hstep := st226_t204
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p205 : ((4399525964907/1250000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 205, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 205, stT226 (i+1))
      = (∑ i ∈ Finset.range 204, stT226 (i+1)) + stT226 205 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 204
    simpa using h
  have hprev := st226_p204
  have hstep := st226_t205
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p206 : ((35200664720257/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 206, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 206, stT226 (i+1))
      = (∑ i ∈ Finset.range 205, stT226 (i+1)) + stT226 206 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 205
    simpa using h
  have hprev := st226_p205
  have hstep := st226_t206
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p207 : ((35820337544849/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 207, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 207, stT226 (i+1))
      = (∑ i ∈ Finset.range 206, stT226 (i+1)) + stT226 207 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 206
    simpa using h
  have hprev := st226_p206
  have hstep := st226_t207
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p208 : ((36384932006099/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 208, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 208, stT226 (i+1))
      = (∑ i ∈ Finset.range 207, stT226 (i+1)) + stT226 208 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 207
    simpa using h
  have hprev := st226_p207
  have hstep := st226_t208
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p209 : ((1134174741627/312500000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 209, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 209, stT226 (i+1))
      = (∑ i ∈ Finset.range 208, stT226 (i+1)) + stT226 209 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 208
    simpa using h
  have hprev := st226_p208
  have hstep := st226_t209
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p210 : ((2227977516957/625000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 210, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 210, stT226 (i+1))
      = (∑ i ∈ Finset.range 209, stT226 (i+1)) + stT226 210 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 209
    simpa using h
  have hprev := st226_p209
  have hstep := st226_t210
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p211 : ((35127322190967/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 211, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 211, stT226 (i+1))
      = (∑ i ∈ Finset.range 210, stT226 (i+1)) + stT226 211 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 210
    simpa using h
  have hprev := st226_p210
  have hstep := st226_t211
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p212 : ((35271630279999/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 212, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 212, stT226 (i+1))
      = (∑ i ∈ Finset.range 211, stT226 (i+1)) + stT226 212 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 211
    simpa using h
  have hprev := st226_p211
  have hstep := st226_t212
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p213 : ((35927081805987/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 213, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 213, stT226 (i+1))
      = (∑ i ∈ Finset.range 212, stT226 (i+1)) + stT226 213 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 212
    simpa using h
  have hprev := st226_p212
  have hstep := st226_t213
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p214 : ((36421099115297/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 214, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 214, stT226 (i+1))
      = (∑ i ∈ Finset.range 213, stT226 (i+1)) + stT226 214 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 213
    simpa using h
  have hprev := st226_p213
  have hstep := st226_t214
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p215 : ((9063768733623/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 215, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 215, stT226 (i+1))
      = (∑ i ∈ Finset.range 214, stT226 (i+1)) + stT226 215 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 214
    simpa using h
  have hprev := st226_p214
  have hstep := st226_t215
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p216 : ((17800208322817/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 216, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 216, stT226 (i+1))
      = (∑ i ∈ Finset.range 215, stT226 (i+1)) + stT226 216 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 215
    simpa using h
  have hprev := st226_p215
  have hstep := st226_t216
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p217 : ((35111929966309/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 217, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 217, stT226 (i+1))
      = (∑ i ∈ Finset.range 216, stT226 (i+1)) + stT226 217 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 216
    simpa using h
  have hprev := st226_p216
  have hstep := st226_t217
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p218 : ((8817555407521/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 218, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 218, stT226 (i+1))
      = (∑ i ∈ Finset.range 217, stT226 (i+1)) + stT226 218 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 217
    simpa using h
  have hprev := st226_p217
  have hstep := st226_t218
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p219 : ((17957820506921/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 219, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 219, stT226 (i+1))
      = (∑ i ∈ Finset.range 218, stT226 (i+1)) + stT226 219 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 218
    simpa using h
  have hprev := st226_p218
  have hstep := st226_t219
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p220 : ((9104602184329/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 220, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 220, stT226 (i+1))
      = (∑ i ∈ Finset.range 219, stT226 (i+1)) + stT226 220 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 219
    simpa using h
  have hprev := st226_p219
  have hstep := st226_t220
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p221 : ((3629579255753/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 221, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 221, stT226 (i+1))
      = (∑ i ∈ Finset.range 220, stT226 (i+1)) + stT226 221 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 220
    simpa using h
  have hprev := st226_p220
  have hstep := st226_t221
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p222 : ((35669354077283/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 222, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 222, stT226 (i+1))
      = (∑ i ∈ Finset.range 221, stT226 (i+1)) + stT226 222 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 221
    simpa using h
  have hprev := st226_p221
  have hstep := st226_t222
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p223 : ((35135612893033/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 223, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 223, stT226 (i+1))
      = (∑ i ∈ Finset.range 222, stT226 (i+1)) + stT226 223 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 222
    simpa using h
  have hprev := st226_p222
  have hstep := st226_t223
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p224 : ((35194892763499/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 224, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 224, stT226 (i+1))
      = (∑ i ∈ Finset.range 223, stT226 (i+1)) + stT226 224 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 223
    simpa using h
  have hprev := st226_p223
  have hstep := st226_t224
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p225 : ((35787655504069/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 225, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 225, stT226 (i+1))
      = (∑ i ∈ Finset.range 224, stT226 (i+1)) + stT226 225 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 224
    simpa using h
  have hprev := st226_p224
  have hstep := st226_t225
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p226 : ((36362560595749/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 226, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 226, stT226 (i+1))
      = (∑ i ∈ Finset.range 225, stT226 (i+1)) + stT226 226 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 225
    simpa using h
  have hprev := st226_p225
  have hstep := st226_t226
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p227 : ((36393048048031/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 227, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 227, stT226 (i+1))
      = (∑ i ∈ Finset.range 226, stT226 (i+1)) + stT226 227 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 226
    simpa using h
  have hprev := st226_p226
  have hstep := st226_t227
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p228 : ((35855317708313/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 228, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 228, stT226 (i+1))
      = (∑ i ∈ Finset.range 227, stT226 (i+1)) + stT226 228 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 227
    simpa using h
  have hprev := st226_p227
  have hstep := st226_t228
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p229 : ((7047631539601/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 229, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 229, stT226 (i+1))
      = (∑ i ∈ Finset.range 228, stT226 (i+1)) + stT226 229 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 228
    simpa using h
  have hprev := st226_p228
  have hstep := st226_t229
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p230 : ((35093989317403/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 230, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 230, stT226 (i+1))
      = (∑ i ∈ Finset.range 229, stT226 (i+1)) + stT226 230 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 229
    simpa using h
  have hprev := st226_p229
  have hstep := st226_t230
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p231 : ((17773642000451/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 231, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 231, stT226 (i+1))
      = (∑ i ∈ Finset.range 230, stT226 (i+1)) + stT226 231 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 230
    simpa using h
  have hprev := st226_p230
  have hstep := st226_t231
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p232 : ((3619480772533/1000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 232, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 232, stT226 (i+1))
      = (∑ i ∈ Finset.range 231, stT226 (i+1)) + stT226 232 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 231
    simpa using h
  have hprev := st226_p231
  have hstep := st226_t232
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p233 : ((36469783628023/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 233, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 233, stT226 (i+1))
      = (∑ i ∈ Finset.range 232, stT226 (i+1)) + stT226 233 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 232
    simpa using h
  have hprev := st226_p232
  have hstep := st226_t233
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p234 : ((9034158746431/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 234, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 234, stT226 (i+1))
      = (∑ i ∈ Finset.range 233, stT226 (i+1)) + stT226 234 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 233
    simpa using h
  have hprev := st226_p233
  have hstep := st226_t234
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p235 : ((35485980514267/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 235, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 235, stT226 (i+1))
      = (∑ i ∈ Finset.range 234, stT226 (i+1)) + stT226 235 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 234
    simpa using h
  have hprev := st226_p234
  have hstep := st226_t235
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p236 : ((35074873595737/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 236, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 236, stT226 (i+1))
      = (∑ i ∈ Finset.range 235, stT226 (i+1)) + stT226 236 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 235
    simpa using h
  have hprev := st226_p235
  have hstep := st226_t236
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p237 : ((17624709316079/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 237, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 237, stT226 (i+1))
      = (∑ i ∈ Finset.range 236, stT226 (i+1)) + stT226 237 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 236
    simpa using h
  have hprev := st226_p236
  have hstep := st226_t237
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p238 : ((35858928450479/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 238, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 238, stT226 (i+1))
      = (∑ i ∈ Finset.range 237, stT226 (i+1)) + stT226 238 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 237
    simpa using h
  have hprev := st226_p237
  have hstep := st226_t238
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p239 : ((7278517350003/2000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 239, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 239, stT226 (i+1))
      = (∑ i ∈ Finset.range 238, stT226 (i+1)) + stT226 239 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 238
    simpa using h
  have hprev := st226_p238
  have hstep := st226_t239
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p240 : ((36409773753137/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 240, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 240, stT226 (i+1))
      = (∑ i ∈ Finset.range 239, stT226 (i+1)) + stT226 240 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 239
    simpa using h
  have hprev := st226_p239
  have hstep := st226_t240
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p241 : ((8974995526481/2500000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 241, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 241, stT226 (i+1))
      = (∑ i ∈ Finset.range 240, stT226 (i+1)) + stT226 241 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 240
    simpa using h
  have hprev := st226_p240
  have hstep := st226_t241
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p242 : ((17640907293637/5000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 242, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 242, stT226 (i+1))
      = (∑ i ∈ Finset.range 241, stT226 (i+1)) + stT226 242 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 241
    simpa using h
  have hprev := st226_p241
  have hstep := st226_t242
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p243 : ((35055325602713/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 243, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 243, stT226 (i+1))
      = (∑ i ∈ Finset.range 242, stT226 (i+1)) + stT226 243 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 242
    simpa using h
  have hprev := st226_p242
  have hstep := st226_t243
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p244 : ((35399327834929/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 244, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 244, stT226 (i+1))
      = (∑ i ∈ Finset.range 243, stT226 (i+1)) + stT226 244 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 243
    simpa using h
  have hprev := st226_p243
  have hstep := st226_t244
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p245 : ((36036173487001/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 245, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 245, stT226 (i+1))
      = (∑ i ∈ Finset.range 244, stT226 (i+1)) + stT226 245 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 244
    simpa using h
  have hprev := st226_p244
  have hstep := st226_t245
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p246 : ((36461006315201/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 246, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 246, stT226 (i+1))
      = (∑ i ∈ Finset.range 245, stT226 (i+1)) + stT226 246 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 245
    simpa using h
  have hprev := st226_p245
  have hstep := st226_t246
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p247 : ((567849516689/156250000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 247, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 247, stT226 (i+1))
      = (∑ i ∈ Finset.range 246, stT226 (i+1)) + stT226 247 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 246
    simpa using h
  have hprev := st226_p246
  have hstep := st226_t247
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p248 : ((35776238371553/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 248, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 248, stT226 (i+1))
      = (∑ i ∈ Finset.range 247, stT226 (i+1)) + stT226 248 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 247
    simpa using h
  have hprev := st226_p247
  have hstep := st226_t248
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p249 : ((35202648804253/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 249, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 249, stT226 (i+1))
      = (∑ i ∈ Finset.range 248, stT226 (i+1)) + stT226 249 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 248
    simpa using h
  have hprev := st226_p248
  have hstep := st226_t249
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_p250 : ((35061089972509/10000000000000 : ℚ) : ℝ)
    ≤ ∑ i ∈ Finset.range 250, stT226 (i+1) := by
  have hsplit : (∑ i ∈ Finset.range 250, stT226 (i+1))
      = (∑ i ∈ Finset.range 249, stT226 (i+1)) + stT226 250 := by
    have h := Finset.sum_range_succ (fun i => stT226 (i+1)) 249
    simpa using h
  have hprev := st226_p249
  have hstep := st226_t250
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem st226_s250 :
    |Real.sin (((226 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))
      - ((-974641/1000000 : ℚ) : ℝ)| ≤ ((1/20000 : ℚ) : ℝ) :=
  sinMulShift_eval (r := -1122801/2500000) (δ := 11473/1000000000) (ψ := -35361/50000) 226 199
    (log_br_250).1 (log_br_250).2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [sinTaylor, Finset.sum_range_succ, Nat.factorial])
    (by norm_num [sinTaylor, cosTaylor, Finset.sum_range_succ, Nat.factorial])

set_option maxHeartbeats 6400000 in
/-- **The certified detector sign at `t = 226`** (evaluated boundary). -/
theorem station_226_sign : hardyG ((((226:ℕ)):ℝ)) < 0 := by
  have hcore := phase_station_lower_eval 226 250 (by norm_num) (by norm_num)
    ((-35361/50000 : ℚ) : ℝ)
  have hchain := st226_p250
  have hbridge : (∑ i ∈ Finset.range 250, stT226 (i+1))
      = ∑ i ∈ Finset.range 250,
          (((i+1 : ℕ)) : ℝ) ^ (-(1/2 : ℝ))
            * Real.cos (((226 : ℕ) : ℝ) * Real.log ((i+1 : ℕ))
              - ((-35361/50000 : ℚ) : ℝ)) := rfl
  rw [hbridge] at hchain
  have hsq := sq_br_250
  have hsh := rpow_half_shifts (N := 250) (by norm_num)
  have hcosb := abs_le.mp st226_c250
  have hsinb := abs_le.mp st226_s250
  have hbdy_lo : ((6968687329287/102152500000000 : ℚ) : ℝ)
      ≤ ((250:ℕ):ℝ) ^ ((1/2:ℝ))
        * (-(Real.cos (((226 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-35361/50000 : ℚ) : ℝ))) / 2
          - ((((226:ℕ)):ℝ))
            * Real.sin (((226 : ℕ) : ℝ) * Real.log ((250 : ℕ)) - ((-35361/50000 : ℚ) : ℝ)))
        / ((1/4 : ℝ) + ((((226:ℕ)):ℝ)) ^ 2) := by
    rw [hsh.1]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 hcosb hsinb ⊢
    have hE : -(Real.cos ((226:ℝ) * Real.log (250:ℝ) - ((-35361/50000 : ℚ) : ℝ))) / 2
        - ((226:ℝ)) * Real.sin ((226:ℝ) * Real.log (250:ℝ) - ((-35361/50000 : ℚ) : ℝ))
        ≥ ((55092357/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hcosb.2, hsinb.2]
    have hsqpos : (0:ℝ) ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ))) := by
      have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ (250:ℝ)) (-(1/2:ℝ))
      positivity
    push_cast
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1/4 + ((226:ℝ)) ^ 2)]
    have h1 := mul_le_mul_of_nonneg_left hE hsqpos
    have hElopos : ((55092357/250000 : ℚ) : ℝ) ≥ 0 := by
      push_cast
      norm_num
    have h2 : (250:ℝ) * (126491/2000000)
          * ((55092357/250000 : ℚ) : ℝ)
        ≤ (250:ℝ) * ((250:ℝ) ^ (-(1/2:ℝ)))
          * ((55092357/250000 : ℚ) : ℝ) := by
      push_cast
      nlinarith [hx, hx0]
    push_cast at h1 h2 ⊢
    linarith [h1, h2]
  have hcost : ((250:ℕ):ℝ) ^ (-(1/2:ℝ)) / 2
      + (((((226:ℕ)):ℝ))+1) * (((((226:ℕ)):ℝ))+2) / 8
        * (((250:ℕ):ℝ) ^ (-(5/2:ℝ)) + ((250:ℕ):ℝ) ^ (-(3/2:ℝ)) / (3/2))
      ≤ ((176450401523/156250000000 : ℚ) : ℝ) := by
    rw [hsh.2.1, hsh.2.2]
    have hx := hsq.2
    have hx0 := hsq.1
    push_cast at hx hx0 ⊢
    nlinarith [hx, hx0]
  have hm : (0:ℝ) < ((35061089972509/10000000000000 : ℚ) : ℝ) + ((6968687329287/102152500000000 : ℚ) : ℝ)
      - ((176450401523/156250000000 : ℚ) : ℝ) := by
    push_cast
    norm_num
  have hP0 : (0:ℝ) < (Complex.exp (((-35361/50000 : ℚ) : ℝ) * Complex.I)
      * riemannZeta (line ((((226:ℕ)):ℝ)))).re := by
    linarith [hcore, hchain, hbdy_lo, hcost, hm]
  have hP : 0 < Real.cos ((-35361/50000 : ℚ) : ℝ)
        * (riemannZeta (line ((((226:ℕ)):ℝ)))).re
      - Real.sin ((-35361/50000 : ℚ) : ℝ)
        * (riemannZeta (line ((((226:ℕ)):ℝ)))).im := by
    rw [← re_phase_eq]
    exact hP0
  have hθ30 := theta30_enclosure
  have hinc := theta_increment_enclosure_from (T₁ := (30:ℝ))
    (T := ((((226:ℕ)):ℝ))) (by norm_num) (by norm_num)
  have hπ := Real.pi_pos
  have hMainM : thetaMain ((((226:ℕ)):ℝ))
      = (((((226:ℕ)):ℝ)) * (Real.log ((((226:ℕ)):ℝ)) - Real.log 2
          - Real.log Real.pi) - ((((226:ℕ)):ℝ))) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  have hMain30 : thetaMain (30:ℝ)
      = ((30:ℝ) * (Real.log (30:ℝ) - Real.log 2 - Real.log Real.pi) - 30) / 2 := by
    rw [thetaMain, Real.log_div (by norm_num) (by positivity),
      Real.log_mul (by norm_num) hπ.ne']
    ring
  rw [hMainM, hMain30] at hinc
  have hlM := log_br_226
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
  have hθwin : |(((-35361/50000 : ℚ) : ℝ) + ((47:ℤ)) * (2*Real.pi) - Real.pi) - theta ((((226:ℕ)):ℝ))| < Real.pi / 2 := by
    rw [abs_lt]
    push_cast at hincb hlM ⊢
    constructor <;> nlinarith [hθb.1, hθb.2, hincb.1, hincb.2,
      hlM.1, hlM.2, hl30.1, hl30.2, hl2.1, hl2.2, hlπ.1, hlπ.2,
      hπ6l, hπ6u]
  have hprox := (hardyG_sign_of_proxy (t := ((((226:ℕ)):ℝ)))
    (φ := ((-35361/50000 : ℚ) : ℝ) + ((47:ℤ)) * (2*Real.pi) - Real.pi) hθwin).2
  apply hprox
  rw [show (((-35361/50000 : ℚ) : ℝ) + ((47:ℤ)) * (2*Real.pi) - Real.pi)
      = ((((-35361/50000 : ℚ)) : ℝ) - Real.pi) + ((47:ℤ)) * (2*Real.pi) by ring,
    (cos_sin_shift ((((-35361/50000 : ℚ)) : ℝ) - Real.pi) 47).1,
    (cos_sin_shift ((((-35361/50000 : ℚ)) : ℝ) - Real.pi) 47).2]
  exact cos_sin_flip ((-35361/50000 : ℚ) : ℝ) _ _ hP

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.station_226_sign
end AxiomAudit
